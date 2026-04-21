package tlc2.tool.impl.jit;

import net.bytebuddy.implementation.Implementation.Context;
import net.bytebuddy.implementation.bytecode.StackManipulation;
import net.bytebuddy.jar.asm.MethodVisitor;
import net.bytebuddy.jar.asm.Opcodes;

public enum OrderManipulation implements StackManipulation {
    Swap(Opcodes.SWAP);


    private final int opcode;

    private OrderManipulation(int opcode) {
        this.opcode = opcode;
    }

    @Override
    public Size apply(MethodVisitor arg0, Context arg1) {
        arg0.visitInsn(opcode);
        return Size.ZERO;
    }

    @Override
    public boolean isValid() {
        return true;
    }    
}
