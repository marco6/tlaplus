package tlc2.tool.impl.jit;

import java.util.ArrayList;

import net.bytebuddy.ByteBuddy;
import net.bytebuddy.asm.AsmVisitorWrapper;
import net.bytebuddy.description.field.FieldDescription;
import net.bytebuddy.description.method.MethodDescription;
import net.bytebuddy.description.modifier.Ownership;
import net.bytebuddy.description.modifier.Visibility;
import net.bytebuddy.description.type.TypeDescription;
import net.bytebuddy.implementation.Implementation;
import net.bytebuddy.implementation.LoadedTypeInitializer;
import net.bytebuddy.implementation.bytecode.ByteCodeAppender;
import net.bytebuddy.implementation.bytecode.Removal;
import net.bytebuddy.implementation.bytecode.StackManipulation;
import net.bytebuddy.implementation.bytecode.assign.TypeCasting;
import net.bytebuddy.implementation.bytecode.constant.IntegerConstant;
import net.bytebuddy.implementation.bytecode.member.FieldAccess;
import net.bytebuddy.implementation.bytecode.member.MethodInvocation;
import net.bytebuddy.implementation.bytecode.member.MethodReturn;
import net.bytebuddy.implementation.bytecode.member.MethodVariableAccess;
import net.bytebuddy.jar.asm.ClassReader;
import net.bytebuddy.jar.asm.ClassWriter;
import net.bytebuddy.jar.asm.MethodVisitor;
import net.bytebuddy.matcher.ElementMatchers;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.Action;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.INextStateFunctor;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.ActionItemList;
import tlc2.tool.impl.FastTool;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.impl.BoolValue;

// TODO: this class can be made "reusable" so `compile` and `compileLambda` can take the action in, instead of the constructor.
public class ActionCompiler extends EvalCompiler {
    private static final int contextLocalIndex = nextStateFunctorLocalIndex + 1; // = 5
    private static final int actionListLocalIndex = contextLocalIndex + 1; // = 6
    public static final int localCount = 2; // context (slot 5) + actionList (slot 6)

    private final FieldDescription actionField;
    private final MethodDescription getNextStatesMethod;
    private final ArrayList<SemanticNode> conjList = new ArrayList<>();

    public ActionCompiler(FastTool tool, Action action,
            ArrayList<SemanticNode> predicates,
            ArrayList<Context> contexts,
            MethodVisitor methodVisitor,
            Implementation.Context context) {
        super(tool, predicates, contexts, action.con, context, true);
        this.actionField = context.getInstrumentedType().getDeclaredFields()
                .filter(ElementMatchers.named("action"))
                .getOnly();
        try {
            this.getNextStatesMethod = new MethodDescription.ForLoadedMethod(
                    Tool.class.getMethod("getNextStates",
                            Action.class, SemanticNode.class, ActionItemList.class, Context.class, TLCState.class,
                            TLCState.class, INextStateFunctor.class, CostModel.class));
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
        this.context = collectConjuctions(action.con, action.pred);
        // actionListLocalIndex occupies the first slot past the static EvalCompiler
        // locals; dynamic locals in this compiler must start after that slot.
        this.nextLocalIndex = actionListLocalIndex + 1;
    }

    private Context collectConjuctions(Context ctx, SemanticNode pred) {
        var newContext = ctx;
        switch (pred.getKind()) {
            case OpApplKind:
                return collectAppl(ctx, (OpApplNode) pred);
            case SubstInKind:
                var subst = (SubstInNode) pred;
                for (var sub : subst.getSubsts()) {
                    var op = sub.getOp();
                    var expr = sub.getExpr();
                    if (expr instanceof OpApplNode) {
                        var exprOp = ((OpApplNode) expr).getOperator();
                        if (op == exprOp) {
                            continue; // Nothing to do here.
                        }
                    }
                    if (expr instanceof OpArgNode) {
                        final SymbolNode opNode = ((OpArgNode) expr).getOp();

                        var val = tool.lookup(opNode, newContext, false);
                        if (val == null) {
                            val = tool.lookup(opNode, context, false);
                        }
                        if (val != null) {
                            newContext = newContext.cons(op, val);
                            continue;
                        }
                    }

                    // We couldn't properly bind the symbol. We can't unwrap this one.
                    conjList.add(pred);
                    return ctx;
                }
                return collectConjuctions(newContext, subst.getBody());
            default:
                conjList.add(pred);
                return ctx;
        }
    }

    private Context collectAppl(Context ctx, OpApplNode pred) {
        var opcode = BuiltInOPs.getOpCode(pred.getOperator().getName());
        switch (opcode) {
            case BuiltInOPs.OPCODE_land:
            case BuiltInOPs.OPCODE_cl:
                for (var arg : pred.getArgs()) {
                    ctx = collectConjuctions(ctx, arg);
                }
                break;
            case 0:
                return collectUserOp(ctx, pred);
            default:
                conjList.add(pred);
                break;
        }
        return ctx;
    }

    private Context collectUserOp(Context ctx, OpApplNode pred) {
        final SymbolNode opNode = pred.getOperator();
        var val = tool.lookup(opNode, ctx, false);

        if (val instanceof OpDefNode) {
            var opDef = (OpDefNode) val;
            int opcode = BuiltInOPs.getOpCode(opDef.getName());
            if (opcode == 0) {
                return collectConjuctions(
                        tool.getOpContext(opDef, pred.getArgs(), ctx, false, CostModel.DO_NOT_RECORD, tool.getId()),
                        opDef.getBody());
            }
        }

        conjList.add(pred);
        return ctx;
    }

    public StackManipulation compileLambda() throws NoSuchMethodException, SecurityException, NoSuchFieldException {
        return new StackManipulation.Compound(
            // Initialize the context local at method entry.
            pushContext(context),
            MethodVariableAccess.REFERENCE.storeAt(contextLocalIndex),
            // Initialize the ActionItemList local from ActionItemList.Empty.
            FieldAccess
                .forField(new FieldDescription.ForLoadedField(ActionItemList.class.getField("Empty")))
                .read(),
            MethodVariableAccess.REFERENCE.storeAt(actionListLocalIndex),
            compile(),
            MethodReturn.VOID);
    }

    public StackManipulation compile()
            throws NoSuchMethodException, SecurityException, NoSuchFieldException {

        var steps = new ArrayList<StackManipulation>();
        var actionPredicates = new ArrayList<SemanticNode>();
        MethodDescription consMethod = new MethodDescription.ForLoadedMethod(ActionItemList.class.getMethod("cons",
                SemanticNode.class, Context.class, CostModel.class, int.class));

        steps.add(IntegerConstant.forValue(1)); // Flag to indicate that the next part should run
        for (var arg : conjList) {
            var conditionPredicateCompiled = compile(arg);
            if (conditionPredicateCompiled == null || topOfStackKind == ResultKind.Void) {
                actionPredicates.add(arg);
            } else {
                var innerSteps = new ArrayList<StackManipulation>();
                innerSteps.add(conditionPredicateCompiled);

                if (topOfStackKind == ResultKind.Value) {
                    innerSteps.add(TypeCasting.to(new TypeDescription.ForLoadedType(BoolValue.class)));
                    innerSteps.add(MethodInvocation
                            .invoke(new MethodDescription.ForLoadedMethod(
                                    BoolValue.class.getMethod("getVal"))));
                    topOfStackKind = ResultKind.Bool;
                }

                if (topOfStackKind != ResultKind.Bool) {
                    throw new IllegalStateException(
                            "Inlined predicate must return a boolean, but got " + topOfStackKind);
                }

                // If the predicate is false, short-circuit and exit.
                steps.add(new RunIf(new StackManipulation.Compound(innerSteps)));
            }
        }

        if (!actionPredicates.isEmpty()) {
            var innerSteps = new ArrayList<StackManipulation>();
            innerSteps.add(MethodVariableAccess.REFERENCE.loadFrom(actionListLocalIndex));
            for (int i = actionPredicates.size() - 1; i > 0; i--) {
                innerSteps.add(pushPredicate(actionPredicates.get(i)));
                innerSteps.add(MethodVariableAccess.REFERENCE.loadFrom(contextLocalIndex));
                innerSteps.add(FieldAccess.forField(
                        new FieldDescription.ForLoadedField(CostModel.class.getField("DO_NOT_RECORD")))
                        .read());
                innerSteps.add(IntegerConstant.forValue(i)); // kind
                innerSteps.add(MethodInvocation.invoke(consMethod));
                innerSteps.add(TypeCasting.to(new TypeDescription.ForLoadedType(ActionItemList.class)));
            }
            innerSteps.add(MethodVariableAccess.REFERENCE.storeAt(actionListLocalIndex));
            // Now call next states with the final action list
            innerSteps.add(MethodVariableAccess.REFERENCE.loadFrom(toolLocalIndex));
            innerSteps.add(pushAction());
            innerSteps.add(pushPredicate(actionPredicates.get(0)));
            innerSteps.add(MethodVariableAccess.REFERENCE.loadFrom(actionListLocalIndex));
            innerSteps.add(MethodVariableAccess.REFERENCE.loadFrom(contextLocalIndex));
            innerSteps.add(MethodVariableAccess.REFERENCE.loadFrom(prevStateLocalIndex));
            innerSteps.add(MethodVariableAccess.REFERENCE.loadFrom(curStateLocalIndex));
            innerSteps.add(MethodVariableAccess.REFERENCE.loadFrom(nextStateFunctorLocalIndex));
            innerSteps.add(FieldAccess
                    .forField(
                            new FieldDescription.ForLoadedField(CostModel.class.getField("DO_NOT_RECORD")))
                    .read());
            innerSteps.add(MethodInvocation.invoke(getNextStatesMethod));
            innerSteps.add(MethodVariableAccess.REFERENCE.storeAt(curStateLocalIndex));
            // RunIf's true branch must leave a guard boolean on the operand stack.
            innerSteps.add(IntegerConstant.forValue(1));
            steps.add(new RunIf(new StackManipulation.Compound(innerSteps)));
        }
        steps.add(Removal.SINGLE);
        topOfStackKind = ResultKind.Void;
        return new StackManipulation.Compound(steps);
    }

    private StackManipulation pushAction() {
        return FieldAccess.forField(this.actionField).read();
    }

    public static CompiledAction delegate(FastTool tool, Action action) {
        return new CompiledAction() {
            @Override
            public void apply(FastTool tool, TLCState state, TLCState nextState, INextStateFunctor nss) {
                tool.getNextStates(action, action.pred, ActionItemList.Empty, action.con, state, nextState, nss,
                        action.cm);
            }
        };
    }

    public static CompiledAction compile(FastTool tool, Action action)
            throws NoSuchMethodException, SecurityException, NoSuchFieldException {
        var predicates = new ArrayList<SemanticNode>();
        var contexts = new ArrayList<Context>();
        var compiledClass = new ByteBuddy()
                .subclass(Object.class)
                .visit(new AsmVisitorWrapper.ForDeclaredMethods()
                        .readerFlags(ClassReader.EXPAND_FRAMES)
                        .writerFlags(ClassWriter.COMPUTE_MAXS | ClassWriter.COMPUTE_FRAMES))
                .implement(CompiledAction.class)
                .defineField("action", Action.class, Visibility.PRIVATE, Ownership.STATIC)
                .defineField("predicates", SemanticNode[].class, Visibility.PRIVATE, Ownership.STATIC)
                .defineField("contexts", Context[].class, Visibility.PRIVATE, Ownership.STATIC)
                // Implement the apply method
                .method(ElementMatchers.isDeclaredBy(CompiledAction.class))
                .intercept(new Implementation.Simple((methodVisitor, context, instrumentedMethod) -> {
                    var compiler = new ActionCompiler(tool, action, predicates, contexts, methodVisitor, context);
                    StackManipulation pipeline;
                    try {
                        pipeline = compiler.compileLambda();
                    } catch (Exception e) {
                        throw new RuntimeException(e);
                    }
                    var stackSize = pipeline.apply(methodVisitor, context);
                    return new ByteCodeAppender.Size(stackSize.getMaximalSize(),
                            instrumentedMethod.getStackSize() + ActionCompiler.localCount);
                }))
                .initializer(new LoadedTypeInitializer.ForStaticField("action", action))
                .initializer(
                        new LoadedTypeInitializer() {
                            @Override
                            public boolean isAlive() {
                                return true;
                            }

                            public void onLoad(java.lang.Class<?> arg0) {
                                new LoadedTypeInitializer.ForStaticField("predicates",
                                        predicates.toArray(new SemanticNode[0])).onLoad(arg0);
                                new LoadedTypeInitializer.ForStaticField("contexts",
                                        contexts.toArray(new Context[0])).onLoad(arg0);
                            };
                        })
                .make().load(ActionCompiler.class.getClassLoader()).getLoaded();
        try {

            var compiledObj = compiledClass.getConstructor()
                    .newInstance();
            return (CompiledAction) compiledObj;
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }
}
