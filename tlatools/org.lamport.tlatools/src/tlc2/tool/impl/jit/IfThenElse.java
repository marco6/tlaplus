package tlc2.tool.impl.jit;

import net.bytebuddy.implementation.Implementation;
import net.bytebuddy.implementation.bytecode.StackManipulation;
import net.bytebuddy.jar.asm.Label;
import net.bytebuddy.jar.asm.MethodVisitor;
import net.bytebuddy.jar.asm.Opcodes;

public class IfThenElse implements StackManipulation{
    private final StackManipulation thenAction;
    private final StackManipulation elseAction;

    public IfThenElse(StackManipulation thenAction, StackManipulation elseAction) {
        this.thenAction = thenAction;
        this.elseAction = elseAction;
    }

    @Override
    public boolean isValid() {
        return thenAction.isValid() && elseAction.isValid();
    }

    @Override
    public Size apply(MethodVisitor methodVisitor, Implementation.Context implementationContext) {
        Label elseLabel = new Label();
        Label endLabel = new Label();

        // 1. The stack currently has a boolean (int) on top.
        // IFEQ pops the top int. If it equals 0 (false), it jumps to the elseLabel.
        methodVisitor.visitJumpInsn(Opcodes.IFEQ, elseLabel);

        // 2. Execute the THEN block
        Size thenSize = thenAction.apply(methodVisitor, implementationContext);

        // Jump over the ELSE block to the end
        methodVisitor.visitJumpInsn(Opcodes.GOTO, endLabel);

        // 3. Execute the ELSE block
        methodVisitor.visitLabel(elseLabel);

        // (Note: ByteBuddy automatically computes StackMapFrames for us,
        // so we don't need to manually calculate frame state here).
        Size elseSize = elseAction.apply(methodVisitor, implementationContext);

        // 4. Mark the end of the statement
        methodVisitor.visitLabel(endLabel);

        // 5. Calculate the overall impact on the stack size.
        // We popped 1 item (the boolean) before executing the branch.
        int sizeImpact = thenSize.getSizeImpact() - 1;

        // The maximum stack depth is the highest depth reached by either branch
        int maxSize = Math.max(thenSize.getMaximalSize(), elseSize.getMaximalSize());

        return new Size(sizeImpact, maxSize);
    }
}
