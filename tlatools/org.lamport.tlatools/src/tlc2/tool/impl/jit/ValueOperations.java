package tlc2.tool.impl.jit;

import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.EvalControl;
import tlc2.tool.TLCState;
import tlc2.tool.ToolGlobals;
import util.Assert;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.ContextEnumerator;
import tlc2.tool.impl.FastTool;
import tlc2.util.Context;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Enumerable;
import tlc2.value.impl.FcnLambdaValue;
import tlc2.value.impl.FcnParams;
import tlc2.value.impl.FunctionValue;
import tlc2.value.impl.Reducible;
import tlc2.value.impl.SetCapValue;
import tlc2.value.impl.SetCupValue;
import tlc2.value.impl.SetDiffValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.SetPredValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueExcept;
import tlc2.value.impl.ValueEnumeration;
import tlc2.value.impl.ValueVec;
import tlc2.value.impl.TupleValue;

public final class ValueOperations {

    private ValueOperations() {
        // utility class
    }

    public static boolean boundedExists(FastTool tool, OpApplNode expr, SemanticNode body, Context c, TLCState s0, TLCState s1) {
        ContextEnumerator Enum = tool.contexts(expr, c, s0, s1, 0, CostModel.DO_NOT_RECORD);
        Context c1;
        while ((c1 = Enum.nextElement()) != null) {
            Value bval = tool.eval(body, c1, s0, s1, 0, CostModel.DO_NOT_RECORD);
            if (!(bval instanceof BoolValue)) {
                Assert.fail(EC.TLC_EXPECTED_VALUE, new String[] { "boolean", expr.toString() }, body, c1);
            }
            if (((BoolValue) bval).val) {
                return true;
            }
        }
        return false;
    }

    public static boolean boundedForall(FastTool tool, OpApplNode expr, SemanticNode body, Context c, TLCState s0,
            TLCState s1) {
        ContextEnumerator Enum = tool.contexts(expr, c, s0, s1, 0, CostModel.DO_NOT_RECORD);
        Context c1;
        while ((c1 = Enum.nextElement()) != null) {
            Value bval = tool.eval(body, c1, s0, s1, 0, CostModel.DO_NOT_RECORD);
            if (!(bval instanceof BoolValue)) {
                Assert.fail(EC.TLC_EXPECTED_VALUE, new String[] { "boolean", expr.toString() }, body, c1);
            }
            if (!((BoolValue) bval).val) {
                return false;
            }
        }
        return true;
    }

    public static Value boundedChoose(FastTool tool, OpApplNode expr, Context c, TLCState s0, TLCState s1) {
        SemanticNode pred = expr.getArgs()[0];
        SemanticNode inExpr = expr.getBdedQuantBounds()[0];
        Value inVal = tool.eval(inExpr, c, s0, s1, 0, CostModel.DO_NOT_RECORD);
        if (!(inVal instanceof Enumerable)) {
            Assert.fail("Attempted to compute the value of an expression of\n"
                    + "form CHOOSE x \\in S: P, but S was not enumerable.\n" + expr, expr, c);
        }

        inVal.normalize();

        ValueEnumeration enumSet = ((Enumerable) inVal).elements(Enumerable.Ordering.NORMALIZED);
        FormalParamNode[] bvars = expr.getBdedQuantSymbolLists()[0];
        boolean isTuple = expr.isBdedQuantATuple()[0];

        if (isTuple) {
            int cnt = bvars.length;
            Value val;
            while ((val = enumSet.nextElement()) != null) {
                TupleValue tv = (TupleValue) val.toTuple();
                if (tv == null || tv.size() != cnt) {
                    Assert.fail("Attempted to compute the value of an expression of form\n"
                            + "CHOOSE <<x1, ... , xN>> \\in S: P, but S was not a set\n"
                            + "of N-tuples.\n" + expr, expr, c);
                }
                Context c1 = c;
                for (int i = 0; i < cnt; i++) {
                    c1 = c1.cons(bvars[i], tv.elems[i]);
                }
                Value bval = tool.eval(pred, c1, s0, s1, 0, CostModel.DO_NOT_RECORD);
                if (!(bval instanceof BoolValue)) {
                    Assert.fail(EC.TLC_EXPECTED_VALUE, new String[] { "boolean", expr.toString() }, pred, c1);
                }
                if (((BoolValue) bval).val) {
                    return val;
                }
            }
        } else {
            SymbolNode name = bvars[0];
            Value val;
            while ((val = enumSet.nextElement()) != null) {
                Context c1 = c.cons(name, val);
                Value bval = tool.eval(pred, c1, s0, s1, 0, CostModel.DO_NOT_RECORD);
                if (!(bval instanceof BoolValue)) {
                    Assert.fail(EC.TLC_EXPECTED_VALUE, new String[] { "boolean", expr.toString() }, pred, c1);
                }
                if (((BoolValue) bval).val) {
                    return val;
                }
            }
        }

        Assert.fail("Attempted to compute the value of an expression of form\n"
                + "CHOOSE x \\in S: P, but no element of S satisfied P.\n" + expr, expr, c);
        return null;
    }

    public static Value setOfAll(FastTool tool, OpApplNode expr, SemanticNode body, Context c, TLCState s0,
            TLCState s1) {
        ValueVec vals = new ValueVec();
        ContextEnumerator Enum = tool.contexts(expr, c, s0, s1, 0, CostModel.DO_NOT_RECORD);
        Context c1;
        while ((c1 = Enum.nextElement()) != null) {
            Value val = tool.eval(body, c1, s0, s1, 0, CostModel.DO_NOT_RECORD);
            vals.addElement(val);
        }
        return new SetEnumValue(vals, false);
    }

    public static Value subsetOf(FastTool tool, OpApplNode expr, SemanticNode pred, Context c, TLCState s0,
            TLCState s1) {
        SemanticNode inExpr = expr.getBdedQuantBounds()[0];
        Value inVal = tool.eval(inExpr, c, s0, s1, 0, CostModel.DO_NOT_RECORD);
        boolean isTuple = expr.isBdedQuantATuple()[0];
        FormalParamNode[] bvars = expr.getBdedQuantSymbolLists()[0];

        if (inVal instanceof Reducible) {
            ValueVec vals = new ValueVec();
            ValueEnumeration enumSet = ((Enumerable) inVal).elements();
            Value elem;
            if (isTuple) {
                while ((elem = enumSet.nextElement()) != null) {
                    Context c1 = c;
                    Value[] tuple = ((TupleValue) elem).elems;
                    for (int i = 0; i < bvars.length; i++) {
                        c1 = c1.cons(bvars[i], tuple[i]);
                    }
                    Value bval = tool.eval(pred, c1, s0, s1, 0, CostModel.DO_NOT_RECORD);
                    if (!(bval instanceof BoolValue)) {
                        Assert.fail("Attempted to evaluate an expression of form {x \\in S : P(x)}"
                                + " when P was " + bval.getKindString() + ".\n" + pred, pred, c1);
                    }
                    if (((BoolValue) bval).val) {
                        vals.addElement(elem);
                    }
                }
            } else {
                SymbolNode idName = bvars[0];
                while ((elem = enumSet.nextElement()) != null) {
                    Context c1 = c.cons(idName, elem);
                    Value bval = tool.eval(pred, c1, s0, s1, 0, CostModel.DO_NOT_RECORD);
                    if (!(bval instanceof BoolValue)) {
                        Assert.fail("Attempted to evaluate an expression of form {x \\in S : P(x)}"
                                + " when P was " + bval.getKindString() + ".\n" + pred, pred, c1);
                    }
                    if (((BoolValue) bval).val) {
                        vals.addElement(elem);
                    }
                }
            }
            return new SetEnumValue(vals, inVal.isNormalized());
        }

        if (isTuple) {
            return new SetPredValue(bvars, inVal, pred, tool, c, s0, s1, 0, CostModel.DO_NOT_RECORD);
        }
        return new SetPredValue(bvars[0], inVal, pred, tool, c, s0, s1, 0, CostModel.DO_NOT_RECORD);
    }

    public static Value fcnConstructor(FastTool tool, OpApplNode expr, int opcode, SemanticNode body, Context c,
            TLCState s0, TLCState s1) {
        FormalParamNode[][] formals = expr.getBdedQuantSymbolLists();
        boolean[] isTuples = expr.isBdedQuantATuple();
        ExprNode[] domains = expr.getBdedQuantBounds();

        Value[] dvals = new Value[domains.length];
        boolean isFcnRcd = true;
        for (int i = 0; i < dvals.length; i++) {
            dvals[i] = tool.eval(domains[i], c, s0, s1, 0, CostModel.DO_NOT_RECORD);
            isFcnRcd = isFcnRcd && (dvals[i] instanceof Reducible);
        }

        FcnParams params = new FcnParams(formals, isTuples, dvals);
        FcnLambdaValue fval = new FcnLambdaValue(params, body, tool, c, s0, s1, 0, CostModel.DO_NOT_RECORD);

        if (opcode == ToolGlobals.OPCODE_rfs) {
            SymbolNode fname = expr.getUnbdedQuantSymbols()[0];
            fval.makeRecursive(fname);
            isFcnRcd = false;
        }

        if (isFcnRcd && !EvalControl.isKeepLazy(0)) {
            return (Value) fval.toFcnRcd();
        }
        return fval;
    }

    public static Value setDiff(Value arg1, Value arg2) {
        if (arg1 instanceof Reducible) {
            return ((Reducible) arg1).diff(arg2);
        }
        return new SetDiffValue(arg1, arg2);
    }

    public static Value setCap(Value arg1, Value arg2) {
        if (arg1 instanceof Reducible) {
            return ((Reducible) arg1).cap(arg2);
        } else if (arg2 instanceof Reducible) {
            return ((Reducible) arg2).cap(arg1);
        }
        return new SetCapValue(arg1, arg2);
    }

    public static Value setCup(Value arg1, Value arg2) {
        if (arg1 instanceof Reducible) {
            return ((Reducible) arg1).cup(arg2);
        } else if (arg2 instanceof Reducible) {
            return ((Reducible) arg2).cup(arg1);
        }
        return new SetCupValue(arg1, arg2);
    }

    public static Value domain(Value arg) {
        if (!(arg instanceof FunctionValue)) {
            Assert.fail("Attempted to apply the operator DOMAIN to a non-function\n(" +
                    arg.getKindString() + ")");
        }
        return ((FunctionValue) arg).getDomain();
    }

    public static Value except(FastTool tool, OpApplNode expr, Value result, Context c, TLCState s0, TLCState s1) {
        final ExprOrOpArgNode[] args = expr.getArgs();
        final int alen = args.length;

        for (int i = 1; i < alen; i++) {
            OpApplNode pairNode = (OpApplNode) args[i];
            ExprOrOpArgNode[] pairArgs = pairNode.getArgs();
            SemanticNode[] cmpts = ((OpApplNode) pairArgs[0]).getArgs();

            Value[] lhs = new Value[cmpts.length];
            for (int j = 0; j < lhs.length; j++) {
                lhs[j] = tool.eval(cmpts[j], c, s0, s1, 0, CostModel.DO_NOT_RECORD);
            }

            Value atVal = result.select(lhs);
            if (atVal == null) {
                MP.printWarning(EC.TLC_EXCEPT_APPLIED_TO_UNKNOWN_FIELD, new String[] { args[0].toString() });
            } else {
                Context c1 = c.cons(ToolGlobals.EXCEPT_AT, atVal);
                Value rhs = tool.eval(pairArgs[1], c1, s0, s1, 0, CostModel.DO_NOT_RECORD);
                ValueExcept vex = new ValueExcept(lhs, rhs);
                result = (Value) result.takeExcept(vex);
            }
        }
        return result;
    }
}
