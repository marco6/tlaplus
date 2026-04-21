package tlc2.tool.impl.jit;

import net.bytebuddy.description.method.MethodDescription;
import net.bytebuddy.implementation.Implementation;
import net.bytebuddy.implementation.bytecode.StackManipulation;
import net.bytebuddy.implementation.bytecode.member.MethodInvocation;
import net.bytebuddy.jar.asm.Label;
import net.bytebuddy.jar.asm.MethodVisitor;
import net.bytebuddy.jar.asm.Opcodes;
import tlc2.value.impl.Enumerable;
import tlc2.value.impl.ValueEnumeration;

/**
 * Bytecode emitter for a compiled bounded-forall expression: {@code \A x \in S : P(x)}.
 *
 * <p>Contract for ctor arguments:
 * <ul>
 *   <li>{@code domain}: pushes a Value that is also an Enumerable.</li>
 *   <li>{@code body}: reads {@code xLocal}, pushes int-bool (0/1).</li>
 *   <li>{@code xLocal}: JVM local slot for the current bound variable value.</li>
 * </ul>
 *
 * <p>Equivalent high-level logic:
 * <pre>{@code
 *   ValueEnumeration e = ((Enumerable) domain).elements();
 *   Value x;
 *   while ((x = e.nextElement()) != null) {
 *     xLocal = x;
 *     if (!body(xLocal)) return false;
 *   }
 *   return true;
 * }</pre>
 */
class BoundedForAll implements StackManipulation {

    private static final MethodDescription ELEMENTS;
    private static final MethodDescription NEXT_ELEMENT;

    static {
        try {
            ELEMENTS = new MethodDescription.ForLoadedMethod(Enumerable.class.getMethod("elements"));
            NEXT_ELEMENT = new MethodDescription.ForLoadedMethod(ValueEnumeration.class.getMethod("nextElement"));
        } catch (NoSuchMethodException e) {
            throw new ExceptionInInitializerError(e);
        }
    }

    private final StackManipulation domain;
    private final StackManipulation body;
    private final int xLocal;

    BoundedForAll(StackManipulation domain, StackManipulation body, int xLocal) {
        this.domain = domain;
        this.body = body;
        this.xLocal = xLocal;
    }

    @Override
    public boolean isValid() {
        return domain.isValid() && body.isValid();
    }

    @Override
    public Size apply(MethodVisitor mv, Implementation.Context ctx) {
        Label loopStart = new Label();
        Label exhausted = new Label();
        Label foundFalse = new Label();
        Label end = new Label();

        Size size = domain.apply(mv, ctx);                                          // [ domain ]
        mv.visitTypeInsn(Opcodes.CHECKCAST, "tlc2/value/impl/Enumerable");
        size = size.aggregate(MethodInvocation.invoke(ELEMENTS).apply(mv, ctx));    // [ enum ]

        mv.visitLabel(loopStart);
        mv.visitInsn(Opcodes.DUP);                                                   // [ enum, enum ]
        size = size.aggregate(MethodInvocation.invoke(NEXT_ELEMENT).apply(mv, ctx)); // [ enum, elem? ]
        mv.visitInsn(Opcodes.DUP);                                                   // [ enum, elem?, elem? ]
        mv.visitJumpInsn(Opcodes.IFNULL, exhausted);                                 // [ enum, elem ]

        mv.visitVarInsn(Opcodes.ASTORE, xLocal);                                     // [ enum ]
        size = size.aggregate(body.apply(mv, ctx));                                  // [ enum, bool:int ]
        mv.visitJumpInsn(Opcodes.IFEQ, foundFalse);                                  // [ enum ]
        mv.visitJumpInsn(Opcodes.GOTO, loopStart);

        // Exhausted with no counterexample: stack is [ enum, null ] -> true.
        mv.visitLabel(exhausted);
        mv.visitInsn(Opcodes.POP);                                                   // [ enum ]
        mv.visitInsn(Opcodes.POP);                                                   // [ ]
        mv.visitInsn(Opcodes.ICONST_1);                                              // [ 1 ]
        mv.visitJumpInsn(Opcodes.GOTO, end);

        // Found a violating element: stack is [ enum ] -> false.
        mv.visitLabel(foundFalse);
        mv.visitInsn(Opcodes.POP);                                                   // [ ]
        mv.visitInsn(Opcodes.ICONST_0);                                              // [ 0 ]

        mv.visitLabel(end);
        return new Size(1, size.getMaximalSize() + 4);
    }
}
