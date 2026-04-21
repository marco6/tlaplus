package tlc2.tool.impl.jit;

import net.bytebuddy.description.field.FieldDescription;
import net.bytebuddy.description.method.MethodDescription;
import net.bytebuddy.implementation.Implementation;
import net.bytebuddy.implementation.bytecode.StackManipulation;
import net.bytebuddy.implementation.bytecode.member.FieldAccess;
import net.bytebuddy.implementation.bytecode.member.MethodInvocation;
import net.bytebuddy.jar.asm.Label;
import net.bytebuddy.jar.asm.MethodVisitor;
import net.bytebuddy.jar.asm.Opcodes;
import tla2sany.semantic.SemanticNode;
import tlc2.value.impl.Enumerable;
import tlc2.value.impl.ValueEnumeration;
import util.Assert;

/**
 * Bytecode emitter for {@code CHOOSE x \in S : P(x)}.
 *
 * <p>
 * Contract:
 * <ul>
 * <li>{@code domain} — pushes a {@code Value} (also {@link Enumerable}) already
 * normalized;
 * caller is responsible for calling {@code normalize()} before handing it to
 * us.</li>
 * <li>{@code body} — reads the bound variable from {@code xLocal}; pushes
 * int-bool (0/1).</li>
 * <li>{@code exprPredicate} — the {@code SemanticNode} of the whole expression,
 * used only
 * as the error-site argument to {@link Assert#fail} if no element matches.</li>
 * <li>{@code xLocal} — JVM local slot for the current element.</li>
 * </ul>
 *
 * <p>
 * Equivalent logic:
 * 
 * <pre>{@code
 * ValueEnumeration e = ((Enumerable) domain).elements(Enumerable.Ordering.NORMALIZED);
 * Value x;
 * while ((x = e.nextElement()) != null) {
 *     xLocal = x;
 *     if (body(xLocal))
 *         return x; // x is already in xLocal, re-load it
 * }
 * Assert.fail("CHOOSE ... but no element satisfied P", expr, null);
 * // unreachable, but the bytecode still pushes a Value to satisfy the verifier
 * }</pre>
 * 
 * Net stack effect: pushes one reference ({@code Value}).
 */
class BoundedChoose implements StackManipulation {

    private static final MethodDescription ELEMENTS_ORDERED;
    private static final MethodDescription NEXT_ELEMENT;
    private static final MethodDescription ASSERT_FAIL_3;
    private static final FieldDescription ORDERING_NORMALIZED;

    static {
        try {
            ELEMENTS_ORDERED = new MethodDescription.ForLoadedMethod(
                    Enumerable.class.getMethod("elements", Enumerable.Ordering.class));
            NEXT_ELEMENT = new MethodDescription.ForLoadedMethod(
                    ValueEnumeration.class.getMethod("nextElement"));
            ASSERT_FAIL_3 = new MethodDescription.ForLoadedMethod(
                    Assert.class.getMethod("fail", String.class, SemanticNode.class, tlc2.util.Context.class));
            ORDERING_NORMALIZED = new FieldDescription.ForLoadedField(
                    Enumerable.Ordering.class.getField("NORMALIZED"));
        } catch (ReflectiveOperationException e) {
            throw new ExceptionInInitializerError(e);
        }
    }

    private final StackManipulation domain;
    private final StackManipulation body;
    private final StackManipulation exprLoader; // pushes SemanticNode for error site
    private final int xLocal;

    /**
     * @param domain     compiled domain — leaves a normalized, enumerable
     *                   {@code Value} on stack
     * @param body       compiled predicate — reads {@code xLocal}; leaves int-bool
     *                   on stack
     * @param exprLoader pushes the {@code SemanticNode} of the CHOOSE expression
     *                   (for error reporting)
     * @param xLocal     JVM local variable slot for the bound variable
     */
    BoundedChoose(StackManipulation domain, StackManipulation body,
            StackManipulation exprLoader, int xLocal) {
        this.domain = domain;
        this.body = body;
        this.exprLoader = exprLoader;
        this.xLocal = xLocal;
    }

    @Override
    public boolean isValid() {
        return domain.isValid() && body.isValid() && exprLoader.isValid();
    }

    @Override
    public Size apply(MethodVisitor mv, Implementation.Context ctx) {
        Label loopStart = new Label();
        Label foundMatch = new Label();
        Label noMatch = new Label();
        Label end = new Label();

        // domain → cast → elements(NORMALIZED)
        Size size = domain.apply(mv, ctx); // [ domain ]
        mv.visitTypeInsn(Opcodes.CHECKCAST, "tlc2/value/impl/Enumerable");
        size = size.aggregate(FieldAccess.forField(ORDERING_NORMALIZED).read()
                .apply(mv, ctx)); // [ enum, NORMALIZED ]
        size = size.aggregate(MethodInvocation.invoke(ELEMENTS_ORDERED)
                .apply(mv, ctx)); // [ iter ]

        // Loop: DUP iter, call nextElement, DUP result, null-check
        mv.visitLabel(loopStart);
        mv.visitInsn(Opcodes.DUP); // [ iter, iter ]
        // NEXT_ELEMENT is inside the loop, so dry-run it to get its Size but DON'T aggregate
        // into the cumulative size (the loop is balanced: starts and ends with [iter])
        Size nextElementSize = MethodInvocation.invoke(NEXT_ELEMENT).apply(mv, ctx); // [ iter, elem? ]
        mv.visitInsn(Opcodes.DUP); // [ iter, elem?, elem? ]
        mv.visitJumpInsn(Opcodes.IFNULL, noMatch); // [ iter, elem ]

        // Store into bound local and evaluate predicate
        mv.visitInsn(Opcodes.DUP);
        mv.visitVarInsn(Opcodes.ASTORE, xLocal); // [ iter, elem ]
        mv.visitInsn(Opcodes.POP); // [ iter ]
        // body is inside the loop, so dry-run it but DON'T aggregate
        // (the IFNE will pop the bool, leaving balanced [iter])
        Size bodySize = body.apply(mv, ctx); // [ iter, bool:int ]
        mv.visitJumpInsn(Opcodes.IFNE, foundMatch); // [ iter ]
        mv.visitJumpInsn(Opcodes.GOTO, loopStart);

        // Match found: xLocal holds the satisfying element.
        mv.visitLabel(foundMatch);
        mv.visitInsn(Opcodes.POP); // pop iter // [ ]
        mv.visitVarInsn(Opcodes.ALOAD, xLocal); // [ result ]
        mv.visitJumpInsn(Opcodes.GOTO, end);

        // No element found: call Assert.fail, then push null (satisfies verifier;
        // unreachable).
        mv.visitLabel(noMatch);
        mv.visitInsn(Opcodes.POP); // pop null // [ iter ]
        mv.visitInsn(Opcodes.POP); // pop iter // [ ]
        mv.visitLdcInsn("Attempted to compute the value of an expression of form\n"
                + "CHOOSE x \\in S: P, but no element of S satisfied P."); // [ msg ]
        size = size.aggregate(exprLoader.apply(mv, ctx)); // [ msg, expr ]
        mv.visitInsn(Opcodes.ACONST_NULL); // [ msg, expr, null ]
        size = size.aggregate(MethodInvocation.invoke(ASSERT_FAIL_3).apply(mv, ctx)); // [ ]
        mv.visitInsn(Opcodes.ACONST_NULL); // [ null ] (unreachable)

        mv.visitLabel(end);
        // Stack: [ Value ]
        // Calculate maximalSize accounting for loop ops that we didn't aggregate
        int maxLoopDepth = Math.max(nextElementSize.getMaximalSize(), bodySize.getMaximalSize());
        int overallMaxSize = size.getMaximalSize() + maxLoopDepth + 2; // +2 for safety margin
        return new Size(1, overallMaxSize);
    }
}
