package tlc2.tool.impl.jit;

import net.bytebuddy.description.method.MethodDescription;
import net.bytebuddy.description.type.TypeDescription;
import net.bytebuddy.implementation.Implementation;
import net.bytebuddy.implementation.bytecode.StackManipulation;
import net.bytebuddy.implementation.bytecode.TypeCreation;
import net.bytebuddy.implementation.bytecode.member.MethodInvocation;
import net.bytebuddy.jar.asm.Label;
import net.bytebuddy.jar.asm.MethodVisitor;
import net.bytebuddy.jar.asm.Opcodes;
import tlc2.value.impl.Enumerable;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueEnumeration;
import tlc2.value.impl.ValueVec;

/**
 * Bytecode emitter for subset filtering: {x \in S : P(x)}.
 *
 * Contract:
 * - domain loads the already-computed domain value.
 * - bindingSetup prepares bound-variable locals from elemLocal (tuple destructuring, etc.).
 * - body evaluates predicate and leaves int-bool (0/1) on stack.
 */
class BoundedSubsetOf implements StackManipulation {

    private static final MethodDescription ELEMENTS;
    private static final MethodDescription NEXT_ELEMENT;
    private static final MethodDescription VALUEVEC_CTOR;
    private static final MethodDescription VALUEVEC_ADD;
    private static final MethodDescription VALUE_IS_NORMALIZED;
    private static final MethodDescription SETENUM_CTOR;

    static {
        try {
            ELEMENTS = new MethodDescription.ForLoadedMethod(
                    Enumerable.class.getMethod("elements"));
            NEXT_ELEMENT = new MethodDescription.ForLoadedMethod(
                    ValueEnumeration.class.getMethod("nextElement"));
            VALUEVEC_CTOR = TypeDescription.ForLoadedType.of(ValueVec.class)
                    .getDeclaredMethods()
                    .filter(net.bytebuddy.matcher.ElementMatchers.isConstructor().and(
                            net.bytebuddy.matcher.ElementMatchers.takesArguments(0)))
                    .getOnly();
            VALUEVEC_ADD = new MethodDescription.ForLoadedMethod(
                    ValueVec.class.getMethod("addElement", Value.class));
            VALUE_IS_NORMALIZED = new MethodDescription.ForLoadedMethod(
                    Value.class.getMethod("isNormalized"));
            SETENUM_CTOR = TypeDescription.ForLoadedType.of(SetEnumValue.class)
                    .getDeclaredMethods()
                    .filter(net.bytebuddy.matcher.ElementMatchers.isConstructor().and(
                            net.bytebuddy.matcher.ElementMatchers
                                    .takesArguments(ValueVec.class, boolean.class)))
                    .getOnly();
        } catch (ReflectiveOperationException e) {
            throw new ExceptionInInitializerError(e);
        }
    }

    private final StackManipulation domain;
    private final StackManipulation bindingSetup;
    private final StackManipulation body;
    private final int domainLocal;
    private final int iterLocal;
    private final int valsLocal;
    private final int elemLocal;

    BoundedSubsetOf(StackManipulation domain, StackManipulation bindingSetup, StackManipulation body,
            int domainLocal, int iterLocal, int valsLocal, int elemLocal) {
        this.domain = domain;
        this.bindingSetup = bindingSetup;
        this.body = body;
        this.domainLocal = domainLocal;
        this.iterLocal = iterLocal;
        this.valsLocal = valsLocal;
        this.elemLocal = elemLocal;
    }

    @Override
    public boolean isValid() {
        return domain.isValid() && bindingSetup.isValid() && body.isValid();
    }

    @Override
    public Size apply(MethodVisitor mv, Implementation.Context ctx) {
        final Label loop = new Label();
        final Label skipAdd = new Label();
        final Label done = new Label();

        Size size = domain.apply(mv, ctx); // [domain]
        mv.visitTypeInsn(Opcodes.CHECKCAST, "tlc2/value/impl/Enumerable");
        size = size.aggregate(MethodInvocation.invoke(ELEMENTS).apply(mv, ctx)); // [iter]
        mv.visitVarInsn(Opcodes.ASTORE, iterLocal);

        size = size.aggregate(TypeCreation.of(TypeDescription.ForLoadedType.of(ValueVec.class)).apply(mv, ctx));
        mv.visitInsn(Opcodes.DUP);
        size = size.aggregate(MethodInvocation.invoke(VALUEVEC_CTOR).apply(mv, ctx));
        mv.visitVarInsn(Opcodes.ASTORE, valsLocal);

        mv.visitLabel(loop);
        mv.visitVarInsn(Opcodes.ALOAD, iterLocal);
        size = size.aggregate(MethodInvocation.invoke(NEXT_ELEMENT).apply(mv, ctx)); // [elem?]
        mv.visitInsn(Opcodes.DUP);
        mv.visitJumpInsn(Opcodes.IFNULL, done); // null branch keeps one null on stack

        mv.visitVarInsn(Opcodes.ASTORE, elemLocal); // []

        size = size.aggregate(bindingSetup.apply(mv, ctx));
        size = size.aggregate(body.apply(mv, ctx)); // [bool]
        mv.visitJumpInsn(Opcodes.IFEQ, skipAdd);

        mv.visitVarInsn(Opcodes.ALOAD, valsLocal);
        mv.visitVarInsn(Opcodes.ALOAD, elemLocal);
        size = size.aggregate(MethodInvocation.invoke(VALUEVEC_ADD).apply(mv, ctx));

        mv.visitLabel(skipAdd);
        mv.visitJumpInsn(Opcodes.GOTO, loop);

        mv.visitLabel(done);
        mv.visitInsn(Opcodes.POP); // pop null

        size = size.aggregate(TypeCreation.of(TypeDescription.ForLoadedType.of(SetEnumValue.class)).apply(mv, ctx));
        mv.visitInsn(Opcodes.DUP);
        mv.visitVarInsn(Opcodes.ALOAD, valsLocal);
        mv.visitVarInsn(Opcodes.ALOAD, domainLocal);
        size = size.aggregate(MethodInvocation.invoke(VALUE_IS_NORMALIZED).apply(mv, ctx));
        size = size.aggregate(MethodInvocation.invoke(SETENUM_CTOR).apply(mv, ctx));

        return new Size(1, size.getMaximalSize() + 4);
    }
}
