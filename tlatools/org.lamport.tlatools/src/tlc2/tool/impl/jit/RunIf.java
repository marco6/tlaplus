package tlc2.tool.impl.jit;

import net.bytebuddy.implementation.Implementation.Context;
import net.bytebuddy.implementation.bytecode.Duplication;
import net.bytebuddy.implementation.bytecode.Removal;
import net.bytebuddy.implementation.bytecode.StackManipulation;
import net.bytebuddy.jar.asm.Label;
import net.bytebuddy.jar.asm.MethodVisitor;
import net.bytebuddy.jar.asm.Opcodes;

public class RunIf implements StackManipulation {
    private final StackManipulation inner;

    public RunIf(StackManipulation inner) {
        this.inner = inner;
    }

    @Override
    public boolean isValid() {
        return inner.isValid();
    }

    @Override
    public Size apply(MethodVisitor methodVisitor, Context implementationContext) {
        Label caseFalse = new Label();

        // 1. DUP -> [ bool, bool ]
        Size size = Duplication.SINGLE.apply(methodVisitor, implementationContext);

        // 2. IFEQ caseFalse -> [ bool ]
        // Pops the top bool. If it was 0 (false), it jumps to caseFalse.
        methodVisitor.visitJumpInsn(Opcodes.IFEQ, caseFalse);

        // --- caseTrue: ---
        // 3. POP -> [ ]
        // We are going to run the user logic, so we clear the leftover duplicated bool.
        size = size.aggregate(Removal.SINGLE.apply(methodVisitor, implementationContext));

        // 4. <user logic> -> [ bool ]
        // The user logic executes on an empty stack (relative to this block)
        // and pushes exactly one boolean.
        size = size.aggregate(inner.apply(methodVisitor, implementationContext));

        // --- caseFalse: ---
        // 5. Merge point.
        // If it jumped, the stack is [ bool ] (the original false).
        // If it ran caseTrue, the stack is [ bool ] (the new result).
        methodVisitor.visitLabel(caseFalse);

        // Calculate stack size impact:
        // The net impact is 0 (we consumed 1 bool, and left 1 bool).
        // Max size is whichever took more room: the DUP instruction (+1), or the user
        // logic.
        return size;
    }
}
