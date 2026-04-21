package tlc2.tool.impl.jit;

import tlc2.tool.TLCState;
import tlc2.tool.impl.FastTool;

public interface CompiledPredicate {
    boolean apply(final FastTool tool, TLCState prevState, TLCState nextState);
}
