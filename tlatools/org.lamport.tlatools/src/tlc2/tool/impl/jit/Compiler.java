package tlc2.tool.impl.jit;

import java.util.ArrayList;

import net.bytebuddy.description.field.FieldDescription;
import net.bytebuddy.description.method.MethodDescription;
import net.bytebuddy.description.type.TypeDescription;
import net.bytebuddy.implementation.Implementation;
import net.bytebuddy.implementation.bytecode.StackManipulation;
import net.bytebuddy.implementation.bytecode.assign.TypeCasting;
import net.bytebuddy.implementation.bytecode.collection.ArrayAccess;
import net.bytebuddy.implementation.bytecode.constant.IntegerConstant;
import net.bytebuddy.implementation.bytecode.member.FieldAccess;
import net.bytebuddy.implementation.bytecode.member.MethodInvocation;
import net.bytebuddy.matcher.ElementMatchers;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.ToolGlobals;
import tlc2.tool.impl.FastTool;
import tlc2.util.Context;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.IntValue;

abstract class Compiler implements ToolGlobals {
    // Args
    protected static final int toolLocalIndex = 1;
    protected static final int prevStateLocalIndex = 2;
    protected static final int curStateLocalIndex = 3;
    // Action-only argument slot. Eval lambdas reserve this slot as a shadow local
    // to keep the remaining local numbering identical.
    protected static final int nextStateFunctorLocalIndex = 4;
    protected static final int argCount = 4;

    protected final FastTool tool;
    protected final ArrayList<SemanticNode> predicates;
    protected final ArrayList<Context> contexts;
    private final FieldDescription predicatesField, contextsField;

    protected Context context;
    protected ResultKind topOfStackKind = ResultKind.Void;

    public Compiler(FastTool tool,
            ArrayList<SemanticNode> predicates,
            ArrayList<Context> contexts,
            Implementation.Context context) {
        this.tool = tool;
        this.predicates = predicates;
        this.contexts = contexts;

        this.predicatesField = context.getInstrumentedType().getDeclaredFields()
                .filter(ElementMatchers.named("predicates"))
                .getOnly();
        this.contextsField = context.getInstrumentedType().getDeclaredFields()
                .filter(ElementMatchers.named("contexts"))
                .getOnly();

    }

    protected StackManipulation pushPredicate(SemanticNode pred) {
        int predicateId = predicates.size();
        predicates.add(pred);
        return new StackManipulation.Compound(
                FieldAccess.forField(this.predicatesField).read(), // [ predicates ]
                IntegerConstant.forValue(predicateId), // [ predicates, predicateId ]
                ArrayAccess.REFERENCE.load() // [ pred ]
        );
    }

    protected StackManipulation pushContext(Context context) {
        int contextId = contexts.size();
        contexts.add(context);
        return new StackManipulation.Compound(
                FieldAccess.forField(this.contextsField).read(), // [ contexts ]
                IntegerConstant.forValue(contextId), // [ contexts, contextId ]
                ArrayAccess.REFERENCE.load() // [ context ]
        );
    }

    /**
     * Returns a StackManipulation that converts the value currently on top of the
     * stack from {@code topOfStackKind} to {@code target}, or {@code null} if no
     * conversion is needed. Throws if the conversion is not possible.
     */
    protected StackManipulation compileConvertTo(ResultKind target)
            throws NoSuchFieldException, SecurityException, NoSuchMethodException {
        var actual = topOfStackKind;
        if (actual == target) {
            return StackManipulation.Trivial.INSTANCE; // already the right kind, no-op
        }

        switch (target) {
            case Value:
                if (actual == ResultKind.Bool) {
                    topOfStackKind = ResultKind.Value;
                    return new IfThenElse(
                            FieldAccess.forField(new FieldDescription.ForLoadedField(BoolValue.class.getField("ValTrue"))).read(),
                            FieldAccess.forField(new FieldDescription.ForLoadedField(BoolValue.class.getField("ValFalse"))).read());
                } else if (actual == ResultKind.Int) {
                    topOfStackKind = ResultKind.Value;
                    return MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                            IntValue.class.getMethod("gen", int.class)));
                }
                break;
            case Bool:
                if (actual == ResultKind.Value) {
                    topOfStackKind = ResultKind.Bool;
                    return new StackManipulation.Compound(
                            TypeCasting.to(new TypeDescription.ForLoadedType(BoolValue.class)),
                            FieldAccess.forField(new FieldDescription.ForLoadedField(BoolValue.class.getField("val"))).read());
                }
                break;
            case Int:
                if (actual == ResultKind.Value) {
                    topOfStackKind = ResultKind.Int;
                    return new StackManipulation.Compound(
                            TypeCasting.to(new TypeDescription.ForLoadedType(IntValue.class)),
                            FieldAccess.forField(new FieldDescription.ForLoadedField(IntValue.class.getField("val"))).read());
                }
                break;
            default:
                break;
        }

        throw new IllegalStateException(
                "Inlined expression kind mismatch: expected " + target + " but got " + actual);
    }
}
