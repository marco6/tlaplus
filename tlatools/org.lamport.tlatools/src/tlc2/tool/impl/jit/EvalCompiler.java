package tlc2.tool.impl.jit;

import java.util.ArrayList;

import net.bytebuddy.ByteBuddy;
import net.bytebuddy.asm.AsmVisitorWrapper;
import net.bytebuddy.description.field.FieldDescription;
import net.bytebuddy.description.method.MethodDescription;
import net.bytebuddy.description.type.TypeDescription;
import net.bytebuddy.implementation.Implementation;
import net.bytebuddy.implementation.LoadedTypeInitializer;
import net.bytebuddy.implementation.bytecode.ByteCodeAppender;
import net.bytebuddy.implementation.bytecode.Duplication;
import net.bytebuddy.implementation.bytecode.Removal;
import net.bytebuddy.implementation.bytecode.StackManipulation;
import net.bytebuddy.implementation.bytecode.Subtraction;
import net.bytebuddy.implementation.bytecode.TypeCreation;
import net.bytebuddy.implementation.bytecode.assign.TypeCasting;
import net.bytebuddy.implementation.bytecode.collection.ArrayAccess;
import net.bytebuddy.implementation.bytecode.collection.ArrayFactory;
import net.bytebuddy.implementation.bytecode.constant.IntegerConstant;
import net.bytebuddy.implementation.bytecode.member.FieldAccess;
import net.bytebuddy.implementation.bytecode.member.MethodInvocation;
import net.bytebuddy.implementation.bytecode.member.MethodReturn;
import net.bytebuddy.implementation.bytecode.member.MethodVariableAccess;
import net.bytebuddy.jar.asm.ClassReader;
import net.bytebuddy.jar.asm.ClassWriter;
import net.bytebuddy.matcher.ElementMatchers;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.FrontEnd;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateMut;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.FastTool;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IBoolValue;
import tlc2.value.IValue;
import tlc2.value.Values;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.FunctionValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.MethodValue;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.OpRcdValue;
import tlc2.value.impl.OpValue;
import tlc2.value.impl.Enumerable;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.SetOfFcnsValue;
import tlc2.value.impl.SetOfRcdsValue;
import tlc2.value.impl.SetOfTuplesValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.SubsetValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.UnionValue;
import tlc2.value.impl.Value;
import util.UniqueString;

public class EvalCompiler extends Compiler {
    public static final int toolId = FrontEnd.getToolId();

    private final boolean prevStateOnly;

    /**
     * Index of the next JVM local variable slot to allocate for a dynamically
     * bound variable (e.g., a quantifier variable). Starts right after the
     * statically-known slots: this(0), args(1-3).
     * Subclasses that reserve additional static locals must adjust this in
     * their constructor.
     */
    protected int nextLocalIndex = argCount;

    /** Allocates the next available JVM local variable slot. */
    protected int allocateLocal() {
        return nextLocalIndex++;
    }

    /**
     * Returns the total number of extra local variable slots needed beyond
     * the method's argument frame (this + declared parameters) for the
     * {@link CompiledPredicate} interface, which has 3 reference parameters.
     * Pass this value as the second argument to {@link
     * net.bytebuddy.implementation.bytecode.ByteCodeAppender.Size} so that
     * ByteBuddy/ASM allocates enough space for all dynamically allocated locals.
     */
    public int getLocalCount() {
        // CompiledPredicate.apply has: this(1) + tool(1) + prevState(1) + nextState(1)
        // = 4 slots.
        return nextLocalIndex - argCount;
    }

    public EvalCompiler(FastTool tool,
            ArrayList<SemanticNode> predicates,
            ArrayList<Context> contexts,
            Context initialContext,
            Implementation.Context implContext,
            boolean prevStateOnly) {
        super(tool, predicates, contexts, implContext);
        this.context = initialContext;
        this.prevStateOnly = prevStateOnly;
    }

    public StackManipulation compileLambda(SemanticNode expr)
            throws NoSuchMethodException, SecurityException, NoSuchFieldException {
        var compiled = compile(expr);
        if (compiled == null) {
            // Top-level lambda stays callable even if expression cannot be unrolled.
            compiled = compileEvalFallback(expr);
        }

        return new StackManipulation.Compound(
                compiled,
                compileConvertTo(ResultKind.Bool),
                MethodReturn.INTEGER);
    }

    public static CompiledPredicate compile(FastTool tool, SemanticNode expr, Context initialContext,
            boolean prevStateOnly) throws NoSuchMethodException, SecurityException, NoSuchFieldException {
        var predicates = new ArrayList<SemanticNode>();
        var contexts = new ArrayList<Context>();

        var compiledClass = new ByteBuddy()
                .subclass(Object.class)
                .visit(new AsmVisitorWrapper.ForDeclaredMethods()
                        .readerFlags(ClassReader.EXPAND_FRAMES)
                        .writerFlags(ClassWriter.COMPUTE_MAXS | ClassWriter.COMPUTE_FRAMES))
                .implement(CompiledPredicate.class)
                .defineField("predicates", SemanticNode[].class, net.bytebuddy.description.modifier.Visibility.PRIVATE,
                        net.bytebuddy.description.modifier.Ownership.STATIC)
                .defineField("contexts", Context[].class, net.bytebuddy.description.modifier.Visibility.PRIVATE,
                        net.bytebuddy.description.modifier.Ownership.STATIC)
                .method(ElementMatchers.isDeclaredBy(CompiledPredicate.class))
                .intercept(new Implementation.Simple((methodVisitor, context, instrumentedMethod) -> {
                    System.out.println("Generating expression for: " + expr.stn.toString() + "...");
                    var compiler = new EvalCompiler(tool, predicates, contexts, initialContext, context, prevStateOnly);
                    StackManipulation pipeline;
                    try {
                        pipeline = compiler.compileLambda(expr);
                    } catch (Exception e) {
                        throw new RuntimeException(e);
                    }
                    var stackSize = pipeline.apply(methodVisitor, context);
                    System.out.println("Generated expression for: " + expr.stn.toString());
                    return new ByteCodeAppender.Size(stackSize.getMaximalSize(),
                            instrumentedMethod.getStackSize() + compiler.getLocalCount());
                }))
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
                .make().load(EvalCompiler.class.getClassLoader()).getLoaded();
        try {
            return (CompiledPredicate) compiledClass.getConstructor().newInstance();
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    public StackManipulation compile(SemanticNode expr)
            throws NoSuchFieldException, SecurityException, NoSuchMethodException {

        switch (expr.getKind()) {
            case OpApplKind:
                var compiledAppl = compileEvalAppl((OpApplNode) expr);
                if (compiledAppl == null) {
                    break;
                }
                return compiledAppl;
            case NumeralKind:
                topOfStackKind = ResultKind.Int;
                return IntegerConstant.forValue(((NumeralNode) expr).val());
            case StringKind:
                var stringVal = (StringValue)expr.getToolObject(tool.getId());
                if (stringVal == null) {
                    stringVal = new StringValue(((StringNode) expr).getRep());
                    expr.setToolObject(tool.getId(), stringVal);
                }
                return compileValue(expr, stringVal);
            case DecimalKind:
            default:
                break;
        }
        return null;
    }

    private StackManipulation compileEvalFallback(SemanticNode expr)
            throws NoSuchFieldException, SecurityException, NoSuchMethodException {
        topOfStackKind = ResultKind.Value;
        return new StackManipulation.Compound(
                MethodVariableAccess.REFERENCE.loadFrom(toolLocalIndex),
                pushPredicate(expr),
                pushContext(this.context),
                MethodVariableAccess.REFERENCE.loadFrom(prevStateLocalIndex),
                MethodVariableAccess.REFERENCE.loadFrom(curStateLocalIndex),
                IntegerConstant.forValue(0),
                FieldAccess.forField(new FieldDescription.ForLoadedField(CostModel.class.getField("DO_NOT_RECORD")))
                        .read(),
                MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(Tool.class.getMethod("eval",
                        SemanticNode.class, Context.class, TLCState.class, TLCState.class, int.class,
                        CostModel.class))));
    }

    private StackManipulation compileEvalAppl(OpApplNode expr)
            throws NoSuchFieldException, SecurityException, NoSuchMethodException {
        final ExprOrOpArgNode[] args = expr.getArgs();
        final SymbolNode opNode = expr.getOperator();
        int opcode = BuiltInOPs.getOpCode(opNode.getName());
        var steps = new ArrayList<StackManipulation>();

        switch (opcode) {
            case OPCODE_eq:
                var eqExpr = compileEquality(args[0], args[1]);
                if (eqExpr == null) {
                    return null;
                }
                steps.add(eqExpr);
                break;
            case OPCODE_noteq:
                var neqExpr = compileEquality(args[0], args[1]);
                if (neqExpr == null) {
                    return null;
                }
                steps.add(neqExpr);
                steps.add(IntegerConstant.forValue(1));
                steps.add(LogicalManipulation.XOR);
                topOfStackKind = ResultKind.Bool;
                break;
            case OPCODE_equiv:
                var leftEquiv = compile(args[0]);
                if (leftEquiv == null) {
                    return null;
                }
                steps.add(leftEquiv);
                steps.add(compileConvertTo(ResultKind.Bool));

                var rightEquiv = compile(args[1]);
                if (rightEquiv == null) {
                    return null;
                }
                steps.add(rightEquiv);
                steps.add(compileConvertTo(ResultKind.Bool));

                // P <=> Q == ~(P XOR Q)
                steps.add(LogicalManipulation.XOR);
                steps.add(IntegerConstant.forValue(1));
                steps.add(LogicalManipulation.XOR);
                topOfStackKind = ResultKind.Bool;
                break;
            case OPCODE_cl:
            case OPCODE_land:
                var conjunction = compileConjunction(args);
                if (conjunction == null) {
                    return null;
                }
                steps.add(conjunction);
                topOfStackKind = ResultKind.Bool;
                break;
            case OPCODE_dl:
            case OPCODE_lor:
                var disjunction = compileDisjunction(args);
                if (disjunction == null) {
                    return null;
                }
                steps.add(disjunction);
                topOfStackKind = ResultKind.Bool;
                break;
            case OPCODE_implies: {
                var impliesLeft = compile(args[0]);
                if (impliesLeft == null) {
                    return null;
                }
                steps.add(impliesLeft);
                steps.add(compileConvertTo(ResultKind.Bool));
                var impliesRight = compile(args[1]);
                if (impliesRight == null) {
                    return null;
                }
                var impliesRightBool = new StackManipulation.Compound(impliesRight, compileConvertTo(ResultKind.Bool));
                // If left is true, evaluate right; if left is false, short-circuit with true.
                steps.add(new IfThenElse(impliesRightBool, IntegerConstant.forValue(1)));
                topOfStackKind = ResultKind.Bool;
                break;
            }
            case OPCODE_ite: {
                var iteCond = compile(args[0]);
                if (iteCond == null) {
                    return null;
                }
                steps.add(iteCond);
                steps.add(compileConvertTo(ResultKind.Bool));

                var iteThen = compile(args[1]);
                if (iteThen == null) {
                    return null;
                }
                var iteThenKind = topOfStackKind;

                var iteElse = compile(args[2]);
                if (iteElse == null) {
                    return null;
                }
                var iteElseKind = topOfStackKind;

                // Use the common kind if both branches agree; otherwise box both to Value.
                var iteTargetKind = (iteThenKind == iteElseKind) ? iteThenKind : ResultKind.Value;

                topOfStackKind = iteThenKind;
                var iteThenFull = new StackManipulation.Compound(iteThen, compileConvertTo(iteTargetKind));
                topOfStackKind = iteElseKind;
                var iteElseFull = new StackManipulation.Compound(iteElse, compileConvertTo(iteTargetKind));

                steps.add(new IfThenElse(iteThenFull, iteElseFull));
                topOfStackKind = iteTargetKind;
                break;
            }
            case OPCODE_case: {
                // Tuple per branch: [0]=condition(bool), [1]=value expr, [2]=value kind
                var caseBranches = new ArrayList<Object[]>();
                StackManipulation otherVal = null;
                ResultKind otherKind = null;
                ResultKind caseTargetKind = null;

                for (var arg : args) {
                    var pairNode = (OpApplNode) arg;
                    var pairArgs = pairNode.getArgs();
                    if (pairArgs[0] == null) {
                        var compiledOther = compile(pairArgs[1]);
                        if (compiledOther == null) {
                            return null;
                        }
                        otherVal = compiledOther;
                        otherKind = topOfStackKind;
                        if (caseTargetKind == null) {
                            caseTargetKind = otherKind;
                        } else if (caseTargetKind != otherKind) {
                            caseTargetKind = ResultKind.Value;
                        }
                    } else {
                        var compiledCond = compile(pairArgs[0]);
                        if (compiledCond == null) {
                            return null;
                        }
                        var condKind = topOfStackKind;
                        topOfStackKind = condKind;
                        var condBool = new StackManipulation.Compound(compiledCond, compileConvertTo(ResultKind.Bool));

                        var compiledVal = compile(pairArgs[1]);
                        if (compiledVal == null) {
                            return null;
                        }
                        var compiledValKind = topOfStackKind;
                        caseBranches.add(new Object[] {
                                condBool,
                                compiledVal,
                                compiledValKind });

                        if (caseTargetKind == null) {
                            caseTargetKind = compiledValKind;
                        } else if (caseTargetKind != compiledValKind) {
                            caseTargetKind = ResultKind.Value;
                        }
                    }
                }

                // Without OTHER, CASE failure semantics are handled by interpreter fallback.
                if (otherVal == null || otherKind == null || caseTargetKind == null) {
                    return null;
                }

                topOfStackKind = otherKind;
                StackManipulation caseAction = new StackManipulation.Compound(
                        otherVal,
                        compileConvertTo(caseTargetKind));

                for (int i = caseBranches.size() - 1; i >= 0; i--) {
                    var branch = caseBranches.get(i);
                    topOfStackKind = (ResultKind) branch[2];
                    var thenAction = new StackManipulation.Compound(
                            (StackManipulation) branch[1],
                            compileConvertTo(caseTargetKind));

                    caseAction = new StackManipulation.Compound(
                            (StackManipulation) branch[0],
                            new IfThenElse(thenAction, caseAction));
                }

                steps.add(caseAction);
                topOfStackKind = caseTargetKind;
                break;
            }
            case OPCODE_lnot:
                var notExpr = compile(args[0]);
                if (notExpr == null) {
                    return null;
                }
                steps.add(notExpr);
                steps.add(compileConvertTo(ResultKind.Bool));
                steps.add(IntegerConstant.forValue(1));
                steps.add(LogicalManipulation.XOR);
                topOfStackKind = ResultKind.Bool;
                break;
            case OPCODE_subset: {
                var subsetExpr = compile(args[0]);
                if (subsetExpr == null) {
                    return null;
                }
                var subsetClass = TypeDescription.ForLoadedType.of(SubsetValue.class);
                var subsetCtor = subsetClass.getDeclaredMethods()
                        .filter(ElementMatchers.isConstructor().and(ElementMatchers.takesArguments(Value.class)))
                        .getOnly();
                steps.add(subsetExpr);
                steps.add(compileConvertTo(ResultKind.Value));
                steps.add(TypeCreation.of(subsetClass));
                steps.add(Duplication.SINGLE.flipOver(TypeDescription.ForLoadedType.of(Value.class).asGenericType()));
                // Stack after flipOver is [uninit, arg, uninit]. Swap to [uninit, uninit, arg]
                // so invokespecial consumes (receiver, arg) in the right order.
                steps.add(OrderManipulation.Swap);
                steps.add(MethodInvocation.invoke(subsetCtor));
                topOfStackKind = ResultKind.Value;
                break;
            }
            case OPCODE_union: {
                var unionExpr = compile(args[0]);
                if (unionExpr == null) {
                    return null;
                }
                steps.add(unionExpr);
                steps.add(compileConvertTo(ResultKind.Value));
                steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                        UnionValue.class.getMethod("union", Value.class))));
                topOfStackKind = ResultKind.Value;
                break;
            }
            case OPCODE_domain: {
                var domainExpr = compile(args[0]);
                if (domainExpr == null) {
                    return null;
                }
                steps.add(domainExpr);
                steps.add(compileConvertTo(ResultKind.Value));
                steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                        ValueOperations.class.getMethod("domain", Value.class))));
                topOfStackKind = ResultKind.Value;
                break;
            }
            case OPCODE_tup: {
                if (args.length == 0) {
                    steps.add(FieldAccess.forField(new FieldDescription.ForLoadedField(
                            TupleValue.class.getField("EmptyTuple"))).read());
                    topOfStackKind = ResultKind.Value;
                    break;
                }
                var tupleClass = TypeDescription.ForLoadedType.of(TupleValue.class);
                var tupleCtor = tupleClass.getDeclaredMethods()
                        .filter(ElementMatchers.isConstructor().and(ElementMatchers.takesArguments(Value[].class)))
                        .getOnly();
                var elements = new ArrayList<StackManipulation>();
                for (int i = 0; i < args.length; i++) {
                    var tupleArg = compile(args[i]);
                    if (tupleArg == null) {
                        return null;
                    }
                    elements.add(new StackManipulation.Compound(tupleArg, compileConvertTo(ResultKind.Value)));
                }

                steps.add(ArrayFactory.forType(TypeDescription.ForLoadedType.of(Value.class).asGenericType())
                        .withValues(elements));
                steps.add(TypeCreation.of(tupleClass));
                steps.add(Duplication.SINGLE.flipOver(TypeDescription.ForLoadedType.of(Value[].class).asGenericType()));
                steps.add(MethodInvocation.invoke(tupleCtor));
                topOfStackKind = ResultKind.Value;
                break;
            }
            case OPCODE_cp: {
                var cpClass = TypeDescription.ForLoadedType.of(SetOfTuplesValue.class);
                var cpCtor = cpClass.getDeclaredMethods()
                        .filter(ElementMatchers.isConstructor().and(ElementMatchers.takesArguments(Value[].class)))
                        .getOnly();
                var elements = new ArrayList<StackManipulation>();
                for (int i = 0; i < args.length; i++) {
                    var cpArg = compile(args[i]);
                    if (cpArg == null) {
                        return null;
                    }
                    elements.add(new StackManipulation.Compound(cpArg, compileConvertTo(ResultKind.Value)));
                }

                steps.add(ArrayFactory.forType(TypeDescription.ForLoadedType.of(Value.class).asGenericType())
                        .withValues(elements));
                steps.add(TypeCreation.of(cpClass));
                steps.add(Duplication.SINGLE.flipOver(TypeDescription.ForLoadedType.of(Value[].class).asGenericType()));
                steps.add(MethodInvocation.invoke(cpCtor));
                topOfStackKind = ResultKind.Value;
                break;
            }
            case OPCODE_rc: {
                var rcClass = TypeDescription.ForLoadedType.of(RecordValue.class);
                var rcCtor = rcClass.getDeclaredMethods()
                        .filter(ElementMatchers.isConstructor().and(ElementMatchers
                                .takesArguments(UniqueString[].class, Value[].class, boolean.class)))
                        .getOnly();
                var nameElements = new ArrayList<StackManipulation>();
                var valueElements = new ArrayList<StackManipulation>();

                for (int i = 0; i < args.length; i++) {
                    var pairNode = (OpApplNode) args[i];
                    var pairArgs = pairNode.getArgs();

                    nameElements.add(new StackManipulation.Compound(
                            pushPredicate(pairArgs[0]),
                            IntegerConstant.forValue(tool.getId()),
                            MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                                    SemanticNode.class.getMethod("getToolObject", int.class))),
                            TypeCasting.to(new TypeDescription.ForLoadedType(StringValue.class)),
                            MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                                    StringValue.class.getMethod("getVal")))));

                    var compiledVal = compile(pairArgs[1]);
                    if (compiledVal == null) {
                        return null;
                    }
                    valueElements.add(new StackManipulation.Compound(compiledVal, compileConvertTo(ResultKind.Value)));
                }

                steps.add(TypeCreation.of(rcClass));
                steps.add(Duplication.SINGLE);
                steps.add(ArrayFactory.forType(TypeDescription.ForLoadedType.of(UniqueString.class).asGenericType())
                        .withValues(nameElements));
                steps.add(ArrayFactory.forType(TypeDescription.ForLoadedType.of(Value.class).asGenericType())
                        .withValues(valueElements));
                steps.add(IntegerConstant.forValue(0)); // isNorm = false
                steps.add(MethodInvocation.invoke(rcCtor));
                topOfStackKind = ResultKind.Value;
                break;
            }
            case OPCODE_sor: {
                var sorClass = TypeDescription.ForLoadedType.of(SetOfRcdsValue.class);
                var sorCtor = sorClass.getDeclaredMethods()
                        .filter(ElementMatchers.isConstructor().and(ElementMatchers
                                .takesArguments(UniqueString[].class, Value[].class, boolean.class)))
                        .getOnly();
                var nameElements = new ArrayList<StackManipulation>();
                var valueElements = new ArrayList<StackManipulation>();

                for (int i = 0; i < args.length; i++) {
                    var pairNode = (OpApplNode) args[i];
                    var pairArgs = pairNode.getArgs();

                    nameElements.add(new StackManipulation.Compound(
                            pushPredicate(pairArgs[0]),
                            IntegerConstant.forValue(tool.getId()),
                            MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                                    SemanticNode.class.getMethod("getToolObject", int.class))),
                            TypeCasting.to(new TypeDescription.ForLoadedType(StringValue.class)),
                            MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                                    StringValue.class.getMethod("getVal")))));

                    var compiledVal = compile(pairArgs[1]);
                    if (compiledVal == null) {
                        return null;
                    }
                    valueElements.add(new StackManipulation.Compound(compiledVal, compileConvertTo(ResultKind.Value)));
                }

                steps.add(TypeCreation.of(sorClass));
                steps.add(Duplication.SINGLE);
                steps.add(ArrayFactory.forType(TypeDescription.ForLoadedType.of(UniqueString.class).asGenericType())
                        .withValues(nameElements));
                steps.add(ArrayFactory.forType(TypeDescription.ForLoadedType.of(Value.class).asGenericType())
                        .withValues(valueElements));
                steps.add(IntegerConstant.forValue(0)); // isNorm = false
                steps.add(MethodInvocation.invoke(sorCtor));
                topOfStackKind = ResultKind.Value;
                break;
            }
            case OPCODE_exc: {
                // ValueOperations.except recursively calls tool.eval on subexpressions.
                // Keep all-or-nothing unrolling: reject this opcode in JIT.
                return null;
            }
            case OPCODE_fa:
                if (args.length != 2) {
                    return null; // Let it crash at runtime.
                }
                steps.add(compile(args[0]));
                if (topOfStackKind != ResultKind.Value) {
                    throw new IllegalStateException(
                            "Expected a function value as the first argument of a function application, but got "
                                    + topOfStackKind);
                }
                steps.add(TypeCasting.to(new TypeDescription.ForLoadedType(FunctionValue.class)));
                var faArgExpr = compile(args[1]);
                if (faArgExpr == null) {
                    return null;
                }
                steps.add(faArgExpr);
                steps.add(compileConvertTo(ResultKind.Value));
                steps.add(IntegerConstant.forValue(0)); // control
                steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                        FunctionValue.class.getMethod("apply", Value.class, int.class))));
                topOfStackKind = ResultKind.Value;
                break;
            case OPCODE_rs:
                if (args[1] instanceof StringNode) {
                    var rsExpr = compile(args[0]);
                    if (rsExpr == null) {
                        return null;
                    }
                    steps.add(rsExpr);
                    steps.add(compileConvertTo(ResultKind.Value));
                    steps.add(IntegerConstant.forValue(((StringNode) args[1]).getRep().getTok()));
                    steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                            Values.class.getMethod("select", Value.class, int.class))));
                    topOfStackKind = ResultKind.Value;
                    break;
                }
                return null;
            case OPCODE_in: {
                var inSetExpr = compile(args[1]);
                if (inSetExpr == null)
                    return null;
                steps.add(inSetExpr);
                steps.add(compileConvertTo(ResultKind.Value));
                var inElemExpr = compile(args[0]);
                if (inElemExpr == null)
                    return null;
                steps.add(inElemExpr);
                steps.add(compileConvertTo(ResultKind.Value));
                steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                        Value.class.getMethod("member", Value.class))));
                topOfStackKind = ResultKind.Bool;
                break;
            }
            case OPCODE_notin: {
                var notinSetExpr = compile(args[1]);
                if (notinSetExpr == null)
                    return null;
                steps.add(notinSetExpr);
                steps.add(compileConvertTo(ResultKind.Value));
                var notinElemExpr = compile(args[0]);
                if (notinElemExpr == null)
                    return null;
                steps.add(notinElemExpr);
                steps.add(compileConvertTo(ResultKind.Value));
                steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                        Value.class.getMethod("member", Value.class))));
                steps.add(IntegerConstant.forValue(1));
                steps.add(LogicalManipulation.XOR);
                topOfStackKind = ResultKind.Bool;
                break;
            }
            case OPCODE_subseteq: {
                var subsetLeftExpr = compile(args[0]);
                if (subsetLeftExpr == null) {
                    return null;
                }
                steps.add(subsetLeftExpr);
                steps.add(compileConvertTo(ResultKind.Value));
                steps.add(TypeCasting.to(new TypeDescription.ForLoadedType(Enumerable.class)));

                var subsetRightExpr = compile(args[1]);
                if (subsetRightExpr == null) {
                    return null;
                }
                steps.add(subsetRightExpr);
                steps.add(compileConvertTo(ResultKind.Value));

                steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                        Enumerable.class.getMethod("isSubsetEq", Value.class))));
                topOfStackKind = ResultKind.Value;
                steps.add(compileConvertTo(ResultKind.Bool));
                break;
            }
            case OPCODE_setdiff: {
                var setdiffLeftExpr = compile(args[0]);
                if (setdiffLeftExpr == null) {
                    return null;
                }
                steps.add(setdiffLeftExpr);
                steps.add(compileConvertTo(ResultKind.Value));

                var setdiffRightExpr = compile(args[1]);
                if (setdiffRightExpr == null) {
                    return null;
                }
                steps.add(setdiffRightExpr);
                steps.add(compileConvertTo(ResultKind.Value));

                steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                        ValueOperations.class.getMethod("setDiff", Value.class, Value.class))));
                topOfStackKind = ResultKind.Value;
                break;
            }
            case OPCODE_cap: {
                var capLeftExpr = compile(args[0]);
                if (capLeftExpr == null) {
                    return null;
                }
                steps.add(capLeftExpr);
                steps.add(compileConvertTo(ResultKind.Value));

                var capRightExpr = compile(args[1]);
                if (capRightExpr == null) {
                    return null;
                }
                steps.add(capRightExpr);
                steps.add(compileConvertTo(ResultKind.Value));

                steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                        ValueOperations.class.getMethod("setCap", Value.class, Value.class))));
                topOfStackKind = ResultKind.Value;
                break;
            }
            case OPCODE_cup: {
                var cupLeftExpr = compile(args[0]);
                if (cupLeftExpr == null) {
                    return null;
                }
                steps.add(cupLeftExpr);
                steps.add(compileConvertTo(ResultKind.Value));

                var cupRightExpr = compile(args[1]);
                if (cupRightExpr == null) {
                    return null;
                }
                steps.add(cupRightExpr);
                steps.add(compileConvertTo(ResultKind.Value));

                steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                        ValueOperations.class.getMethod("setCup", Value.class, Value.class))));
                topOfStackKind = ResultKind.Value;
                break;
            }
            case OPCODE_se:
                topOfStackKind = ResultKind.Value;
                if (args.length == 0) {
                    // Just return SetEnumValue.EmptySet
                    steps.add(FieldAccess
                            .forField(new FieldDescription.ForLoadedField(SetEnumValue.class.getField("EmptySet")))
                            .read());
                } else {
                    var setEnumClass = TypeDescription.ForLoadedType.of(SetEnumValue.class);
                    var setEnumCtor = setEnumClass.getDeclaredMethods()
                            .filter(ElementMatchers.isConstructor()
                                    .and(ElementMatchers
                                            .takesArguments(Value[].class, boolean.class)))
                            .getOnly();

                    var elements = new ArrayList<StackManipulation>();
                    for (int i = 0; i < args.length; i++) {
                        var compiledArg = compile(args[i]);
                        if (compiledArg == null) {
                            return null;
                        }
                        elements.add(new StackManipulation.Compound(compiledArg, compileConvertTo(ResultKind.Value)));
                    }

                    steps.add(TypeCreation.of(setEnumClass));
                    steps.add(Duplication.SINGLE);
                    steps.add(ArrayFactory.forType(TypeDescription.ForLoadedType.of(Value.class).asGenericType())
                            .withValues(elements));
                    steps.add(IntegerConstant.forValue(0)); // not norm
                    steps.add(MethodInvocation.invoke(setEnumCtor));
                }
                break;
            case OPCODE_prime: {
                if (prevStateOnly) {
                    return null;
                }
                var primeExpr = compilePrime(args[0]);
                if (primeExpr == null) {
                    return null;
                }
                steps.add(primeExpr);
                // topOfStackKind already set by compilePrime
                break;
            }
            case OPCODE_unchanged: {
                if (prevStateOnly) {
                    return null;
                }
                var unchangedExpr = compileUnchanged(args[0]);
                if (unchangedExpr == null) {
                    return null;
                }
                steps.add(unchangedExpr);
                // topOfStackKind already set by compileUnchanged
                break;
            }
            case OPCODE_bc: {
                FormalParamNode[][] symbolLists = expr.getBdedQuantSymbolLists();
                boolean[] isTuples = expr.isBdedQuantATuple();
                ExprNode[] domains = expr.getBdedQuantBounds();

                // Single non-tuple variable, single domain (same restriction as exists/forall).
                if (symbolLists.length != 1 || symbolLists[0].length != 1
                        || isTuples[0] || domains.length != 1) {
                    return null;
                }

                FormalParamNode bvar = symbolLists[0][0];
                SemanticNode domainExpr = domains[0];
                SemanticNode body = args[0];

                // Compile domain; normalize it at runtime before enumerating.
                var compiledDomain = compile(domainExpr);
                if (compiledDomain == null) {
                    return null;
                }
                // Normalize and store in a local so we enumerate the stable set.
                int domainLocal = allocateLocal();
                var domainInit = new StackManipulation.Compound(
                        compiledDomain,
                        compileConvertTo(ResultKind.Value),
                        new StackManipulation.Compound(
                                // duplicate so we can call normalize() then reload from local
                                Duplication.SINGLE,
                                MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                                        Value.class.getMethod("normalize"))),
                                Removal.SINGLE, // normalize returns itself as a result, but it's better to keep the typed version instead.
                                MethodVariableAccess.REFERENCE.storeAt(domainLocal)));
                var domainLoader = MethodVariableAccess.REFERENCE.loadFrom(domainLocal);

                // Allocate local for the bound variable.
                int xLocal = allocateLocal();

                // Extend context and compile body.
                var savedContext = this.context;
                this.context = savedContext.cons(bvar, new LocalRef(xLocal, ResultKind.Value));
                var compiledBody = compile(body);
                this.context = savedContext;

                if (compiledBody == null) {
                    return null;
                }
                var bodyWithConvert = new StackManipulation.Compound(
                        compiledBody, compileConvertTo(ResultKind.Bool));

                topOfStackKind = ResultKind.Value;
                return new StackManipulation.Compound(
                        domainInit,
                        new BoundedChoose(domainLoader, bodyWithConvert, pushPredicate(expr), xLocal));
            }
            case OPCODE_be: {
                return compileBoundedQuantifier(expr, args[0], true);
            }
            case OPCODE_bf: {
                return compileBoundedQuantifier(expr, args[0], false);
            }
            case OPCODE_fc:
            case OPCODE_nrfs:
            case OPCODE_rfs: {
                // fcnConstructor uses tool.eval internally.
                return null;
            }
            case OPCODE_soa: {
                // setOfAll uses tool.eval internally.
                return null;
            }
            case OPCODE_sof: {
                if (args.length != 2) {
                    return null;
                }
                var sofClass = TypeDescription.ForLoadedType.of(SetOfFcnsValue.class);
                var sofCtor = sofClass.getDeclaredMethods()
                        .filter(ElementMatchers.isConstructor().and(ElementMatchers
                                .takesArguments(Value.class, Value.class)))
                        .getOnly();
                var compiledDomain = compile(args[0]);
                if (compiledDomain == null) {
                    return null;
                }
                var compiledRange = compile(args[1]);
                if (compiledRange == null) {
                    return null;
                }
                steps.add(TypeCreation.of(sofClass));
                steps.add(Duplication.SINGLE);
                steps.add(compiledDomain);
                steps.add(compileConvertTo(ResultKind.Value));
                steps.add(compiledRange);
                steps.add(compileConvertTo(ResultKind.Value));
                steps.add(MethodInvocation.invoke(sofCtor));
                topOfStackKind = ResultKind.Value;
                break;
            }
            case OPCODE_sso: {
                // SubsetOf: {x \in S : P(x)}
                // Implemented without interpreter eval by iterating the domain and filtering.
                FormalParamNode[][] symbolLists = expr.getBdedQuantSymbolLists();
                boolean[] isTuples = expr.isBdedQuantATuple();
                ExprNode[] domains = expr.getBdedQuantBounds();

                if (args.length != 1 || symbolLists.length != 1 || domains.length != 1) {
                    return null;
                }

                FormalParamNode[] bvars = symbolLists[0];
                if (bvars.length == 0) {
                    return null;
                }

                var compiledDomain = compile(domains[0]);
                if (compiledDomain == null) {
                    return null;
                }

                int domainLocal = allocateLocal();
                int iterLocal = allocateLocal();
                int valsLocal = allocateLocal();
                int elemLocal = allocateLocal();

                var domainInit = new StackManipulation.Compound(
                        compiledDomain,
                        compileConvertTo(ResultKind.Value),
                        MethodVariableAccess.REFERENCE.storeAt(domainLocal));

                var oldContext = this.context;
                var newContext = oldContext;
                StackManipulation bindingSetup = StackManipulation.Trivial.INSTANCE;

                if (isTuples[0]) {
                    var tupleSetup = new ArrayList<StackManipulation>();
                    for (int i = 0; i < bvars.length; i++) {
                        int tupleElemLocal = allocateLocal();
                        newContext = newContext.cons(bvars[i], new LocalRef(tupleElemLocal, ResultKind.Value));
                        tupleSetup.add(MethodVariableAccess.REFERENCE.loadFrom(elemLocal));
                        tupleSetup.add(TypeCasting.to(new TypeDescription.ForLoadedType(TupleValue.class)));
                        tupleSetup.add(FieldAccess.forField(new FieldDescription.ForLoadedField(
                                TupleValue.class.getField("elems"))).read());
                        tupleSetup.add(IntegerConstant.forValue(i));
                        tupleSetup.add(ArrayAccess.REFERENCE.load());
                        tupleSetup.add(MethodVariableAccess.REFERENCE.storeAt(tupleElemLocal));
                    }
                    bindingSetup = new StackManipulation.Compound(tupleSetup);
                } else {
                    if (bvars.length != 1) {
                        return null;
                    }
                    newContext = newContext.cons(bvars[0], new LocalRef(elemLocal, ResultKind.Value));
                }

                this.context = newContext;
                try {
                    var compiledPred = compile(args[0]);
                    if (compiledPred == null) {
                        return null;
                    }

                    var bodyWithBool = new StackManipulation.Compound(
                            compiledPred,
                            compileConvertTo(ResultKind.Bool));

                    topOfStackKind = ResultKind.Value;
                    return new StackManipulation.Compound(
                            domainInit,
                            new BoundedSubsetOf(
                                    MethodVariableAccess.REFERENCE.loadFrom(domainLocal),
                                    bindingSetup,
                                    bodyWithBool,
                                    domainLocal,
                                    iterLocal,
                                    valsLocal,
                                    elemLocal));
                } finally {
                    this.context = oldContext;
                }
            }
            case OPCODE_nop:
                if (args.length != 1) {
                    return null;
                }
                var nopExpr = compile(args[0]);
                if (nopExpr == null) {
                    return null;
                }
                steps.add(nopExpr);
                break;
            case 0:
                return compileUserEvalOp(opNode, args);
            // Intentionally interpreter-only for now.
            case OPCODE_uc:
            case OPCODE_ue:
            case OPCODE_uf:
            default:
                return null;
        }

        return new StackManipulation.Compound(steps);
    }

    /**
     * Recursively compiles UNCHANGED for well-known patterns:
     * - UNCHANGED x : variable → compare s0[x] == s1[x]
     * - UNCHANGED <<e,...>> : tuple → AND of each element (short-circuit)
     * Returns null for any unknown pattern (falls back to interpreter).
     */
    private StackManipulation compileUnchanged(SemanticNode expr)
            throws NoSuchFieldException, SecurityException, NoSuchMethodException {
        if (!(expr instanceof OpApplNode)) {
            return null;
        }
        var appl = (OpApplNode) expr;
        var opNode = appl.getOperator();
        int opcode = BuiltInOPs.getOpCode(opNode.getName());

        // UNCHANGED <<e1, e2, ...>> — recurse into each element with short-circuit AND
        if (opcode == OPCODE_tup) {
            var tupleArgs = appl.getArgs();
            if (tupleArgs.length == 0) {
                topOfStackKind = ResultKind.Bool;
                return IntegerConstant.forValue(1); // UNCHANGED <<>> is trivially true
            }
            var steps = new ArrayList<StackManipulation>();
            steps.add(IntegerConstant.forValue(1)); // accumulator: start with true
            topOfStackKind = ResultKind.Bool;
            for (var arg : tupleArgs) {
                var part = compileUnchanged(arg);
                if (part == null) {
                    return null;
                }
                steps.add(new IfThenElse(part, IntegerConstant.forValue(0)));
                topOfStackKind = ResultKind.Bool;
            }
            return new StackManipulation.Compound(steps);
        }

        // UNCHANGED x — direct variable reference
        if (opNode.getKind() == VariableDeclKind) {
            int varLoc = opNode.getName().getVarLoc();
            topOfStackKind = ResultKind.Bool;
            return new StackManipulation.Compound(
                    MethodVariableAccess.REFERENCE.loadFrom(prevStateLocalIndex),
                    IntegerConstant.forValue(varLoc),
                    MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                            TLCStateMut.class.getMethod("lookup", TLCState.class, int.class))),
                    MethodVariableAccess.REFERENCE.loadFrom(curStateLocalIndex),
                    IntegerConstant.forValue(varLoc),
                    MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                            TLCStateMut.class.getMethod("lookup", TLCState.class, int.class))),
                    MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                            Values.class.getMethod("equals", Value.class, Value.class))));
        }

        return null; // unknown pattern — fall back to interpreter
    }

    /**
     * Recursively compiles prime for well-known patterns:
     * - x' : variable reference in next state
     * - <<e1, ...>>' : tuple of primed subexpressions
     * - Op()' : recurse into zero-arity operator body when resolvable
     * Returns null for unknown patterns (falls back to interpreter).
     */
    private StackManipulation compilePrime(SemanticNode expr)
            throws NoSuchFieldException, SecurityException, NoSuchMethodException {
        if (!(expr instanceof OpApplNode)) {
            return null;
        }
        var appl = (OpApplNode) expr;
        var opNode = appl.getOperator();
        int opcode = BuiltInOPs.getOpCode(opNode.getName());

        // x' -> lookup x in current/next state local.
        if (opNode.getKind() == VariableDeclKind) {
            int varLoc = opNode.getName().getVarLoc();
            topOfStackKind = ResultKind.Value;
            return new StackManipulation.Compound(
                    MethodVariableAccess.REFERENCE.loadFrom(curStateLocalIndex),
                    IntegerConstant.forValue(varLoc),
                    MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                            TLCStateMut.class.getMethod("lookup", TLCState.class, int.class))));
        }

        // <<e1, ...>>' -> tuple of recursively primed elements.
        if (opcode == OPCODE_tup) {
            var tupleArgs = appl.getArgs();
            if (tupleArgs.length == 0) {
                topOfStackKind = ResultKind.Value;
                return FieldAccess.forField(new FieldDescription.ForLoadedField(
                        TupleValue.class.getField("EmptyTuple"))).read();
            }

            var tupleClass = TypeDescription.ForLoadedType.of(TupleValue.class);
            var tupleCtor = tupleClass.getDeclaredMethods()
                    .filter(ElementMatchers.isConstructor().and(ElementMatchers.takesArguments(Value[].class)))
                    .getOnly();
            var elements = new ArrayList<StackManipulation>();
            for (var arg : tupleArgs) {
                var primedElem = compilePrime(arg);
                if (primedElem == null) {
                    return null;
                }
                elements.add(new StackManipulation.Compound(primedElem, compileConvertTo(ResultKind.Value)));
            }

            topOfStackKind = ResultKind.Value;
            return new StackManipulation.Compound(
                    TypeCreation.of(tupleClass),
                    Duplication.SINGLE,
                    ArrayFactory.forType(TypeDescription.ForLoadedType.of(Value.class).asGenericType())
                            .withValues(elements),
                    MethodInvocation.invoke(tupleCtor));
        }

        // Op()' -> unfold zero-arity operator definitions and continue recursively.
        if (opcode == 0 && appl.getArgs().length == 0) {
            final Object val;
            switch (opNode.getKind()) {
                case ConstantDeclKind:
                    val = tool.lookup(opNode);
                    break;
                case FormalParamKind:
                    val = context.lookup(opNode);
                    break;
                default:
                    val = tool.lookup(opNode, context, false);
                    break;
            }

            if (val instanceof OpDefNode) {
                return compilePrime(((OpDefNode) val).getBody());
            }
        }

        return null;
    }

    private StackManipulation compileEquality(ExprOrOpArgNode leftArg, ExprOrOpArgNode rightArg)
            throws NoSuchFieldException, SecurityException, NoSuchMethodException {
        final ArrayList<StackManipulation> steps = new ArrayList<>();

        var left = compile(leftArg);
        if (left == null) {
            return null;
        }
        steps.add(left);
        var leftKind = topOfStackKind;

        var right = compile(rightArg);
        if (right == null) {
            return null;
        }
        steps.add(right);
        var rightKind = topOfStackKind;

        if (leftKind == rightKind) {
            switch (leftKind) {
                case Value:
                    steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                            Values.class.getMethod("equals", Value.class, Value.class))));
                    break;
                case Bool:
                case Int:
                    // Convert primitive comparison into a boolean: (left - right) == 0.
                    steps.add(Subtraction.INTEGER);
                    steps.add(new IfThenElse(IntegerConstant.forValue(0), IntegerConstant.forValue(1)));
                    break;
                default:
                    throw new IllegalStateException("Unsupported equality comparison for type " + leftKind);
            }
        } else if (leftKind == ResultKind.Value && rightKind == ResultKind.Bool) {
            steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                    Values.class.getMethod("equals", Value.class, boolean.class))));
        } else if (leftKind == ResultKind.Bool && rightKind == ResultKind.Value) {
            steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                    Values.class.getMethod("equals", boolean.class, Value.class))));
        } else if (leftKind == ResultKind.Value && rightKind == ResultKind.Int) {
            steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                    Values.class.getMethod("equals", Value.class, int.class))));
        } else if (leftKind == ResultKind.Int && rightKind == ResultKind.Value) {
            steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                    Values.class.getMethod("equals", int.class, Value.class))));
        } else {
            throw new IllegalStateException(
                    "Unsupported equality comparison between types " + leftKind + " and " + rightKind);
        }

        topOfStackKind = ResultKind.Bool;
        return new StackManipulation.Compound(steps);
    }

    private StackManipulation compileConjunction(ExprOrOpArgNode[] args)
            throws NoSuchFieldException, SecurityException, NoSuchMethodException {
        var steps = new ArrayList<StackManipulation>();
        steps.add(IntegerConstant.forValue(1)); // start with true
        topOfStackKind = ResultKind.Bool;

        for (var arg : args) {
            var compiled = compile(arg);
            if (compiled == null) {
                return null;
            }
            var term = new StackManipulation.Compound(compiled, compileConvertTo(ResultKind.Bool));
            // Short-circuit: if current conjunction is false, keep false and skip the rest.
            steps.add(new IfThenElse(term, IntegerConstant.forValue(0)));
            topOfStackKind = ResultKind.Bool;
        }

        return new StackManipulation.Compound(steps);
    }

    private StackManipulation compileDisjunction(ExprOrOpArgNode[] args)
            throws NoSuchFieldException, SecurityException, NoSuchMethodException {
        var steps = new ArrayList<StackManipulation>();
        steps.add(IntegerConstant.forValue(0)); // start with false
        topOfStackKind = ResultKind.Bool;

        for (var arg : args) {
            var compiled = compile(arg);
            if (compiled == null) {
                return null;
            }
            var term = new StackManipulation.Compound(compiled, compileConvertTo(ResultKind.Bool));
            // Short-circuit: if current disjunction is true, keep true and skip the rest.
            steps.add(new IfThenElse(IntegerConstant.forValue(1), term));
            topOfStackKind = ResultKind.Bool;
        }

        return new StackManipulation.Compound(steps);
    }

    private StackManipulation compileUserEvalOp(SymbolNode opNode, ExprOrOpArgNode[] args)
            throws NoSuchFieldException, SecurityException, NoSuchMethodException {
        Object val = null;
        switch (opNode.getKind()) {
            case ConstantDeclKind:
                val = tool.lookup(opNode);
                break;
            case FormalParamKind:
                val = context.lookup(opNode);
                break;
            case VariableDeclKind:
                topOfStackKind = ResultKind.Value;
                return new StackManipulation.Compound(
                        MethodVariableAccess.REFERENCE.loadFrom(prevStateLocalIndex),
                        IntegerConstant.forValue(opNode.getName().getVarLoc()),
                        MethodInvocation
                                .invoke(new MethodDescription.ForLoadedMethod(TLCStateMut.class.getMethod("lookup",
                                        TLCState.class, int.class))));
            default:
                val = tool.lookup(opNode, context, false);
                break;
        }

        if (val instanceof LocalRef) {
            var ref = (LocalRef) val;
            topOfStackKind = ref.kind;
            return MethodVariableAccess.REFERENCE.loadFrom(ref.localIndex);
        }

        if (val instanceof OpDefNode) {
            final OpDefNode opDef = (OpDefNode) val;
            int opcode = BuiltInOPs.getOpCode(opDef.getName());
            if (opcode == 0) {
                final var formals = opDef.getParams();
                if (formals.length != args.length) {
                    return null;
                }

                final ArrayList<StackManipulation> argSetup = new ArrayList<>();
                var newContext = this.context;
                for (int i = 0; i < args.length; i++) {
                    // Guardrail: EvalCompiler only supports value-parameter inlining.
                    // Operator-valued formals still require interpreter context semantics.
                    if (formals[i].getArity() != 0) {
                        return null;
                    }

                    var compiledArg = compile(args[i]);
                    if (compiledArg == null) {
                        return null;
                    }

                    int argLocal = allocateLocal();
                    argSetup.add(compiledArg);
                    argSetup.add(compileConvertTo(ResultKind.Value));
                    argSetup.add(MethodVariableAccess.REFERENCE.storeAt(argLocal));
                    newContext = newContext.cons(formals[i], new LocalRef(argLocal, ResultKind.Value));
                }

                var oldContext = this.context;
                this.context = newContext;
                try {
                    var compiled = compile(opDef.getBody());
                    if (compiled == null) {
                        return null;
                    }
                    argSetup.add(compiled);
                    return new StackManipulation.Compound(argSetup);
                } finally {
                    this.context = oldContext;
                }
            }
        }

        if (val instanceof OpValue) {
            // Must be checked before `val instanceof Value` since OpValue extends Value.
            final ArrayList<StackManipulation> steps = new ArrayList<>();

            for (var arg : args) {
                var compiledArg = compile(arg);
                if (compiledArg == null) {
                    return null;
                }
                steps.add(compiledArg);
                steps.add(compileConvertTo(ResultKind.Value));
            }

            if (val instanceof MethodValue) {
                var method = ((MethodValue) val).md;
                steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(method)));
                var result = method.getReturnType();
                if (result.equals(IBoolValue.class) || result.equals(BoolValue.class)) {
                    topOfStackKind = ResultKind.Bool;
                    steps.add(MethodInvocation
                            .invoke(new MethodDescription.ForLoadedMethod(IBoolValue.class.getMethod("getVal"))));
                } else if (result.equals(IntValue.class)) {
                    topOfStackKind = ResultKind.Int;
                    steps.add(FieldAccess
                            .forField(new FieldDescription.ForLoadedField(IntValue.class.getField("val"))).read());
                } else if (result.equals(IValue.class)) {
                    topOfStackKind = ResultKind.Value;
                    steps.add(TypeCasting.to(new TypeDescription.ForLoadedType(Value.class)));
                }
            } else if (val instanceof OpRcdValue) {
                topOfStackKind = ResultKind.Value;
                steps.add(IntegerConstant.forValue(0)); // control
                steps.add(MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                        OpValue.class.getMethod("eval", Value[].class, int.class))));
            } else {
                // Not supported for now.
                return null;
            }

            return new StackManipulation.Compound(steps);
        } else if (val instanceof Value) {
            return compileValue(opNode, (Value) val);
        } else {
            return null;
        }
    }

    private StackManipulation compileValue(SemanticNode opNode, Value val)
            throws NoSuchMethodException, SecurityException, NoSuchFieldException {

        if (val instanceof ModelValue) {
            topOfStackKind = ResultKind.Value;
            return new StackManipulation.Compound(
                    FieldAccess.forField(new FieldDescription.ForLoadedField(ModelValue.class.getField("mvs")))
                            .read(),
                    IntegerConstant.forValue(((ModelValue) val).index),
                    ArrayAccess.REFERENCE.load());
        } else if (val instanceof IntValue) {
            topOfStackKind = ResultKind.Int;
            return IntegerConstant.forValue(((IntValue) val).val);
        } else if (val instanceof BoolValue) {
            topOfStackKind = ResultKind.Bool;
            return IntegerConstant.forValue(((BoolValue) val).val ? 1 : 0);
        } else if (val instanceof LazyValue) {
            var lazyVal = (LazyValue) val;
            var oldContext = this.context;
            this.context = lazyVal.con;
            var compiled = compile(lazyVal.expr);
            this.context = oldContext;
            if (compiled == null) {
                return null;
            }
            return compiled;
        } else {
            // Plain constant Value (not a callable OpValue). Load it from the tool object.
            var oldToolValue = opNode.getToolObject(tool.getId());
            if (oldToolValue == null) {
                opNode.setToolObject(tool.getId(), val);
            } else if (oldToolValue != val) {
                return null; // Weird.
            }

            topOfStackKind = ResultKind.Value;
            return new StackManipulation.Compound(
                    pushPredicate(opNode),
                    IntegerConstant.forValue(tool.getId()),
                    MethodInvocation.invoke(new MethodDescription.ForLoadedMethod(
                            SemanticNode.class.getMethod("getToolObject", int.class))),
                    TypeCasting.to(new TypeDescription.ForLoadedType(Value.class)));
        }
    }

    private StackManipulation compileBoundedQuantifier(OpApplNode expr, SemanticNode body, boolean exists)
            throws NoSuchFieldException, SecurityException, NoSuchMethodException {
        FormalParamNode[][] symbolLists = expr.getBdedQuantSymbolLists();
        boolean[] isTuples = expr.isBdedQuantATuple();
        ExprNode[] domains = expr.getBdedQuantBounds();

        if (symbolLists.length != 1 || domains.length != 1) {
            return null;
        }

        // Supported shape: a single non-tuple binder group over one domain,
        // with one or more variables, e.g. \A i,j \in Server : body.
        if (isTuples[0] || symbolLists[0].length == 0) {
            return null;
        }

        var variables = new ArrayList<FormalParamNode>(symbolLists[0].length);
        for (var variable : symbolLists[0]) {
            variables.add(variable);
        }

        // Compile the single domain expression and reuse it for all nested levels.
        var compiledDomain = compile(domains[0]);
        if (compiledDomain == null) {
            return null;
        }

        int domainLocal = allocateLocal();
        var domainInit = new StackManipulation.Compound(
                compiledDomain,
                compileConvertTo(ResultKind.Value),
                MethodVariableAccess.REFERENCE.storeAt(domainLocal));

        var domainLoader = MethodVariableAccess.REFERENCE.loadFrom(domainLocal);
        var nested = compileBoundedQuantifierNested(variables, 0, domainLoader, body, exists);
        if (nested == null) {
            return null;
        }

        topOfStackKind = ResultKind.Bool;
        return new StackManipulation.Compound(domainInit, nested);
    }

    private StackManipulation compileBoundedQuantifierNested(ArrayList<FormalParamNode> variables, int index,
            StackManipulation domainLoader, SemanticNode body, boolean exists)
            throws NoSuchFieldException, SecurityException, NoSuchMethodException {
        FormalParamNode bvar = variables.get(index);
        int xLocal = allocateLocal();

        var savedContext = this.context;
        this.context = savedContext.cons(bvar, new LocalRef(xLocal, ResultKind.Value));
        try {
            final StackManipulation inner;
            if (index == variables.size() - 1) {
                var compiledBody = compile(body);
                if (compiledBody == null) {
                    return null;
                }
                inner = new StackManipulation.Compound(compiledBody, compileConvertTo(ResultKind.Bool));
            } else {
                inner = compileBoundedQuantifierNested(variables, index + 1, domainLoader, body, exists);
                if (inner == null) {
                    return null;
                }
            }

            return exists
                    ? new BoundedExists(domainLoader, inner, xLocal)
                    : new BoundedForAll(domainLoader, inner, xLocal);
        } finally {
            this.context = savedContext;
        }
    }
}
