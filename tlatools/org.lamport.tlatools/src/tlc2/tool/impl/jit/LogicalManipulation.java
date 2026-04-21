package tlc2.tool.impl.jit;

import net.bytebuddy.implementation.Implementation;
import net.bytebuddy.implementation.bytecode.StackManipulation;
import net.bytebuddy.jar.asm.MethodVisitor;
import net.bytebuddy.jar.asm.Opcodes;

public enum LogicalManipulation implements StackManipulation {
    XOR(Opcodes.IXOR),
    AND(Opcodes.IAND),
    OR(Opcodes.IOR);

    private final int opcode;

    LogicalManipulation(int opcode) {
        this.opcode = opcode;
    }

    @Override
    public boolean isValid() {
        return true;
    }

    @Override
    public Size apply(MethodVisitor mv, Implementation.Context ctx) {
        mv.visitInsn(opcode);
        return new Size(-1, 0); // Pops two, pushes one = net change of -1
    }
}
