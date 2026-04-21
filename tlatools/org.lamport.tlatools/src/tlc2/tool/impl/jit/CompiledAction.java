package tlc2.tool.impl.jit;

import tlc2.TLC;
import tlc2.tool.INextStateFunctor;
import tlc2.tool.TLCState;
import tlc2.tool.impl.FastTool;

public interface CompiledAction {
    void apply(final FastTool tool, TLCState state, TLCState nextState, final INextStateFunctor functor);
}
