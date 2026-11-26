module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
public import Silmaril.Languages.Python.Core.Module.SeededCall.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Silmaril.Languages.Python.Core.Module.SeededCall (Failure Namespace Value)
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run (Argument Instruction)
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Core.Closure (Function)

theorem observeNestedCallIn_instance {space : Namespace} {context : CallContext}
    {outer inner className : String} {operand : Core.Module.Functions.Operand}
    {value : Value} {kind : Core.Module.SeededCall.Builtin} {result : Bool}
    (helper : space.lookupGlobal outer = some (.helper .assertTrue))
    (probe : space.lookupGlobal inner = some (.builtin .isinstance))
    (evaluated : (lowerCallOperand operand).eval space #v[] = .ok value)
    (classBinding : space.lookupGlobal className = some (.builtin kind))
    (tested : Core.Module.SeededCall.invoke (.builtin .isinstance) [value, .builtin kind] =
      .ok (.bool result)) :
    observeNestedCallIn space context .discard outer
      [.call inner [operand, .readGlobal className]] =
      (⟨if result then .ok none else .error (.raised (.assertionError (.boolean false))),
        [⟨inner, ⟨.ok (.bool result), none⟩⟩,
         ⟨outer, ⟨if result then .ok .none else .error (.raised (.assertionError (.boolean false))), none⟩⟩]⟩,
        context.heap) := by
  have resolved : Core.Module.SeededCall.resolveCall space #v[] (.global inner)
      [lowerCallOperand operand, lowerCallOperand (.readGlobal className)] =
      .ok (.builtin .isinstance, [value, .builtin kind]) := by
    have readClass : (lowerCallOperand (.readGlobal className)).eval space #v[] =
        .ok (.builtin kind) := by
      simp [lowerCallOperand, Core.Module.SeededCall.Operand.eval, classBinding]
    have readProbe : (Core.Module.SeededCall.Operand.global inner).eval space #v[] =
        .ok (.builtin .isinstance) := by
      simp [Core.Module.SeededCall.Operand.eval, probe]
    simp only [Core.Module.SeededCall.resolveCall, Core.Module.SeededCall.Operand.evalList,
      evaluated, readClass, readProbe, Except.bind, Except.map]
  have testedObservation : Core.Module.SeededCall.invokeObserved (.builtin .isinstance)
      [value, .builtin kind] = ⟨.ok (.bool result), none⟩ := by
    cases value <;> cases kind <;>
      exact congrArg (fun outcome => Core.Module.SeededCall.CallObservation.mk outcome none) tested
  have assertionObservation : Core.Module.SeededCall.invokeObserved (.helper .assertTrue) [.bool result] =
      ⟨if result then .ok .none else .error (.raised (.assertionError (.boolean false))), none⟩ := by
    change Core.Module.SeededCall.CallObservation.mk
      (Core.Module.SeededCall.invoke (.helper .assertTrue) [.bool result]) none = _
    cases result <;> simp [Core.Module.SeededCall.invoke_assertTrue_true,
      Core.Module.SeededCall.invoke_assertTrue_false]
  cases result <;>
    simp [observeNestedCallIn, observeRemainingCallIn, observeArgumentsIn, observeArgumentIn, argumentObservation,
      resolved, helper, invokeArgumentIn, invokeNestedTarget, invokeDescriptor, acceptObservation,
      acceptCall, testedObservation, assertionObservation, Except.bind, Except.map, Except.mapError,
      ModuleFailure.ofCall]

theorem observeNestedCallIn_intInstance {space : Namespace} {context : CallContext}
    {outer inner className : String} (value : Int)
    (helper : space.lookupGlobal outer = some (.helper .assertTrue))
    (probe : space.lookupGlobal inner = some (.builtin .isinstance))
    (classBinding : space.lookupGlobal className = some (.builtin .int)) :
    observeNestedCallIn space context .discard outer
      [.call inner [.literal (.int value), .readGlobal className]] =
      (⟨.ok none, [⟨inner, ⟨.ok (.bool true), none⟩⟩, ⟨outer, ⟨.ok .none, none⟩⟩]⟩, context.heap) :=
  observeNestedCallIn_instance helper probe rfl classBinding
    (Core.Module.SeededCall.invoke_isinstance_int_int value)

theorem observeNestedCallIn_innerPreparationError {space : Namespace} {context : CallContext}
    {outer inner : String} {operands : List Core.Module.Functions.Operand} {callee : Value} {error : Failure}
    (outerFound : space.lookupGlobal outer = some callee)
    (failed : Core.Module.SeededCall.resolveCall space #v[] (.global inner) (operands.map lowerCallOperand) =
      .error error) :
    observeNestedCallIn space context .discard outer [.call inner operands] =
      (⟨.error (.ofCall error), [⟨inner, ⟨.error error, none⟩⟩]⟩, context.heap) := by
  simp [observeNestedCallIn, observeRemainingCallIn, observeArgumentsIn, observeArgumentIn, argumentObservation,
    outerFound, failed, Except.mapError]

theorem intDivMod_operand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Core.Closure.Heap) (frame : Core.Closure.Frame layout)
    (op : Core.Closure.IntDivModOp) (numerator divisor : Int) :
    (lowerCallOperand (.intDivMod op numerator divisor)).eval space #v[] =
      (((Core.Module.Functions.Operand.intDivMod op numerator divisor).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) := by
  simp only [lowerCallOperand, Core.Module.SeededCall.Operand.eval, Core.Module.Functions.Operand.lower,
    Core.Closure.Executor.Operand.evalIn]
  cases op.eval numerator divisor <;> rfl

theorem intTrueDiv_operand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Core.Closure.Heap) (frame : Core.Closure.Frame layout)
    (numerator divisor : Int) :
    (lowerCallOperand (.intTrueDiv numerator divisor)).eval space #v[] =
      (((Core.Module.Functions.Operand.intTrueDiv numerator divisor).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) := by
  simp only [lowerCallOperand, Core.Module.SeededCall.Operand.eval, Core.Module.Functions.Operand.lower,
    Core.Closure.Executor.Operand.evalIn]
  cases Core.Closure.trueDivideInt numerator divisor <;> rfl

theorem floatDiv_operand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Core.Closure.Heap) (frame : Core.Closure.Frame layout)
    (operands : Core.Binary64.FloatOperands) :
    (lowerCallOperand (.floatDiv operands)).eval space #v[] =
      (((Core.Module.Functions.Operand.floatDiv operands).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) := by
  simp only [lowerCallOperand, Core.Module.SeededCall.Operand.eval, Core.Module.Functions.Operand.lower,
    Core.Closure.Executor.Operand.evalIn]
  cases Core.Closure.trueDivideFloat operands <;> rfl

private theorem floatArithmeticResult_agrees
    (result : Except Core.Binary64.FloatArithmeticError Silmaril.Numeric.Ieee754.F64.Finite) :
    Core.Module.SeededCall.floatArithmeticResult result =
      ((Core.Closure.floatArithmeticResult result).map seededValue).mapError (fun
        | .defined error => .raised (.runtime error)
        | _ => .unsupported) := by
  cases result with
  | ok _ => rfl
  | error error => cases error <;> rfl

theorem mixedAdd_operand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Core.Closure.Heap) (frame : Core.Closure.Frame layout)
    (integer : Int) (floating : Silmaril.Numeric.Ieee754.F64.Finite) :
    (lowerCallOperand (.mixedAdd integer floating)).eval space #v[] =
      (((Core.Module.Functions.Operand.mixedAdd integer floating).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) :=
  floatArithmeticResult_agrees (Core.Binary64.mixedAdd integer floating)

theorem floatAdd_operand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Core.Closure.Heap) (frame : Core.Closure.Frame layout)
    (left right : Silmaril.Numeric.Ieee754.F64.Finite) :
    (lowerCallOperand (.floatAdd left right)).eval space #v[] =
      (((Core.Module.Functions.Operand.floatAdd left right).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) := by
  simp only [lowerCallOperand, Core.Module.SeededCall.Operand.eval, Core.Module.Functions.Operand.lower,
    Core.Closure.Executor.Operand.evalIn, Core.Closure.floatAdd]
  cases Core.Binary64.addFinite? left right <;> rfl

theorem floatSub_operand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Core.Closure.Heap) (frame : Core.Closure.Frame layout)
    (operands : Core.Binary64.FloatOperands) :
    (lowerCallOperand (.floatSub operands)).eval space #v[] =
      (((Core.Module.Functions.Operand.floatSub operands).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) :=
  floatArithmeticResult_agrees (Core.Binary64.subtract operands)

theorem floatMul_operand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Core.Closure.Heap) (frame : Core.Closure.Frame layout)
    (operands : Core.Binary64.FloatOperands) :
    (lowerCallOperand (.floatMul operands)).eval space #v[] =
      (((Core.Module.Functions.Operand.floatMul operands).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) :=
  floatArithmeticResult_agrees (Core.Binary64.multiply operands)

theorem observeArguments_iff {space : Namespace} {arguments : List Argument}
    {values : Except Failure (List Value)} {calls : List CallEvent} :
    observeArguments space arguments = (values, calls) ↔ EvaluatesArguments space arguments values calls := by
  constructor
  · induction arguments generalizing values calls with
    | nil =>
      intro observed
      cases observed
      exact .nil
    | cons argument rest ih =>
      intro observed
      cases first : observeArgument space argument with
      | mk result firstCalls =>
        cases result with
        | error error =>
          rw [observeArguments, first] at observed
          cases observed
          exact .stop first
        | ok value =>
          cases tail : observeArguments space rest with
          | mk tailValues tailCalls =>
            rw [observeArguments, first, tail] at observed
            cases observed
            exact .next first (ih tail)
  · intro evaluated
    induction evaluated with
    | nil => rfl
    | stop failed => simp [observeArguments, failed]
    | next first _ ih => simp [observeArguments, first, ih]

theorem preserves_builtins {scope : Languages.Python.Source.Scope} (space : Namespace)
    (instructions : List (Instruction scope)) (context : CallContext) (lists : Core.Module.ListHeap) :
    (runInstructionsIn space context instructions lists).residual.builtins = space.builtins := by
  induction instructions generalizing space context lists with
  | nil => rfl
  | cons instruction rest ih =>
    cases selected : (effectWithLists space context instruction lists).1.1.binding with
    | error error => simp [runInstructionsIn, selected]
    | ok binding =>
      cases binding with
      | none => simp [runInstructionsIn, selected, ih]
      | some assignment =>
        obtain ⟨name, value⟩ := assignment
        simp [runInstructionsIn, selected, ih, Namespace.bind_preserves_builtins]


theorem run_directDiscard {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {closure : Function} {rest : List (Instruction scope)}
    (found : space.lookupGlobal name = some (.function closure))
    (admitted : context.acceptsPublishedCall closure = true) :
    runInstructionsIn space context (.call .discard name [] :: rest) =
      let invocation := callbackInvocation space context.heap closure
      match (invocation.runPrefix context.table context.fuel).2.state with
      | .finished heap (.ok value) =>
        let tail := runInstructionsIn space { context with heap } rest
        { tail with calls := ⟨name, ⟨.ok (seededValue value), none⟩⟩ :: tail.calls }
      | .finished heap (.error error) =>
        let failure := callbackError space error
        ⟨space, .error (.ofCall failure), [⟨name, ⟨.error failure, none⟩⟩], heap, Core.Module.ListHeap.empty⟩
      | .faulted heap _ fault => ⟨space, .error (.directCallFault fault), [], heap, Core.Module.ListHeap.empty⟩
      | .running heap .. | .delivering heap .. | .receiving heap .. =>
        ⟨space, .error .directCallFuelExhausted, [], heap, Core.Module.ListHeap.empty⟩ := by
  simp [runInstructionsIn, effectWithLists, effect, Core.Module.SeededCall.resolveCall,
    Core.Module.SeededCall.Operand.eval, found, Core.Module.SeededCall.Operand.evalList,
    Except.bind, Except.map, invokeFlatCall, admitted]
  generalize (callbackInvocation space context.heap closure |>.runPrefix context.table context.fuel).2.state =
    state
  cases state with
  | finished heap result => cases result <;> rfl
  | _ => rfl

theorem run_directDiscard_unsupported {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {closure : Function} {rest : List (Instruction scope)}
    (found : space.lookupGlobal name = some (.function closure))
    (rejected : context.acceptsPublishedCall closure = false) :
    runInstructionsIn space context (.call .discard name [] :: rest) =
      ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], context.heap, Core.Module.ListHeap.empty⟩ := by
  simp [runInstructionsIn, effectWithLists, effect, Core.Module.SeededCall.resolveCall,
    Core.Module.SeededCall.Operand.eval, found, Core.Module.SeededCall.Operand.evalList,
    Except.bind, Except.map, Except.mapError, invokeFlatCall, rejected, acceptObservation, ModuleFailure.ofCall]

theorem factoryOperands_iff {values : List Value} {operands : List Core.Module.Functions.Operand} :
    factoryOperands values = some operands ↔
      ∃ integers : List Int, integers.length ≤ 3 ∧ values = integers.map .int ∧
        operands = integers.map (fun value => .literal (.int value)) := by
  have mapped (values : List Value) (operands : List Core.Module.Functions.Operand) :
      values.mapM factoryOperand = some operands ↔
        ∃ integers : List Int, values = integers.map .int ∧
          operands = integers.map (fun value => .literal (.int value)) := by
    induction values generalizing operands with
    | nil =>
      constructor
      · intro equal
        exact ⟨[], rfl, by simpa using equal.symm⟩
      · rintro ⟨integers, empty, rfl⟩
        cases integers <;> simp_all
    | cons value values ih =>
      constructor
      · intro equal
        cases value with
        | int value =>
          cases tail : values.mapM factoryOperand with
          | none => simp [factoryOperand, tail] at equal
          | some tailOperands =>
            obtain ⟨integers, source, target⟩ := (ih tailOperands).mp tail
            exact ⟨value :: integers, by simp [source], by
              simpa [factoryOperand, tail, target] using equal.symm⟩
        | _ => simp [factoryOperand] at equal
      · rintro ⟨integers, source, rfl⟩
        cases integers with
        | nil => simp at source
        | cons first rest =>
          simp only [List.map_cons, List.cons.injEq] at source
          obtain ⟨rfl, remaining⟩ := source
          have tail := (ih _).mpr ⟨rest, remaining, rfl⟩
          simp [factoryOperand, tail]
  constructor
  · intro accepted
    by_cases length : values.length ≤ 3
    · simp only [factoryOperands, length, ite_true, mapped] at accepted
      obtain ⟨integers, source, target⟩ := accepted
      exact ⟨integers, by simpa [source] using length, source, target⟩
    · simp [factoryOperands, length] at accepted
  · rintro ⟨integers, length, rfl, rfl⟩
    have size : (integers.map Value.int).length ≤ 3 := by simpa using length
    simp only [factoryOperands, size, ite_true, mapped]
    exact ⟨integers, rfl, rfl⟩

theorem run_factory_unrecorded {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name target : String} {closure : Function} {arguments : List Core.Module.Functions.Operand}
    {values : List Value} {rest : List (Instruction scope)}
    (resolved : Core.Module.SeededCall.resolveCall space #v[] (.global name)
      (arguments.map lowerCallOperand) = .ok (.function closure, values))
    (unpublished : closure ∉ context.published) (unescaped : closure ∉ context.escaped) :
    runInstructionsIn space context (.call (.bindGlobal target) name arguments :: rest) =
      ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], context.heap, Core.Module.ListHeap.empty⟩ := by
  have denied (arity : Nat) : context.acceptsFactory closure arity = false := by
    simp [CallContext.acceptsFactory, CallContext.acceptsCallFrom, unpublished, unescaped]
  have deniedTuple (arity : Nat) : context.acceptsTupleResult closure arity = false := by
    simp [CallContext.acceptsTupleResult, CallContext.acceptsPublishedCall, CallContext.acceptsCallFrom, unpublished]
  cases operands : factoryOperands values <;>
    simp [runInstructionsIn, effectWithLists, effect, resolved, invokeFlatCall, operands, denied, deniedTuple,
      invokePublishedFloat, unpublished, acceptObservation, ModuleFailure.ofCall, Except.bind, Except.mapError]

theorem run_factory {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name target : String} {closure : Function} {arguments operands : List Core.Module.Functions.Operand}
    {values : List Value} {rest : List (Instruction scope)}
    (resolved : Core.Module.SeededCall.resolveCall space #v[] (.global name)
      (arguments.map lowerCallOperand) = .ok (.function closure, values))
    (profile : factoryOperands values = some operands)
    (admitted : context.acceptsFactory closure operands.length = true) :
    runInstructionsIn space context (.call (.bindGlobal target) name arguments :: rest) =
      match ordinaryCall space context closure operands with
      | .finished heap (.ok (.function result)) =>
        let tail := runInstructionsIn (space.bindGlobal target (.function result))
          { context with heap, escaped := result :: context.escaped } rest
        { tail with calls := ⟨name, ⟨.ok (.function result), none⟩⟩ :: tail.calls }
      | .finished heap (.ok _) =>
        ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], heap, Core.Module.ListHeap.empty⟩
      | .finished heap (.error error) =>
        let failure := callbackError space error
        ⟨space, .error (.ofCall failure), [⟨name, ⟨.error failure, none⟩⟩], heap, Core.Module.ListHeap.empty⟩
      | .faulted heap _ fault => ⟨space, .error (.directCallFault fault), [], heap, Core.Module.ListHeap.empty⟩
      | .running heap .. | .delivering heap .. | .receiving heap .. =>
        ⟨space, .error .directCallFuelExhausted, [], heap, Core.Module.ListHeap.empty⟩ := by
  simp only [runInstructionsIn, effectWithLists, effect, resolved, invokeFlatCall, profile, admitted, ite_true]
  generalize ordinaryCall space context closure operands = state
  cases state with
  | finished heap result =>
    cases result with
    | ok value => cases value <;> rfl
    | error error => rfl
  | _ => rfl

theorem run_adjacentKeywordDiscard {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {closure : Function} {value : Int} {rest : List (Instruction scope)}
    (found : space.lookupGlobal name = some (.function closure))
    (admitted : context.acceptsPublishedCall closure 1 = true) :
    runInstructionsIn space context (.adjacentKeywordDiscard name value :: rest) =
      let invocation := (callbackSession space context.heap).prepareCall .discard
        (.literal (.function closure)) [.literal (.int value)]
      match (invocation.runPrefix context.table context.fuel).2.state with
      | .finished heap (.ok result) =>
        let tail := runInstructionsIn space { context with heap } rest
        { tail with calls := ⟨name, ⟨.ok (seededValue result), none⟩⟩ :: tail.calls }
      | .finished heap (.error error) =>
        let failure := callbackError space error
        ⟨space, .error (.ofCall failure), [⟨name, ⟨.error failure, none⟩⟩], heap, Core.Module.ListHeap.empty⟩
      | .faulted heap _ fault => ⟨space, .error (.directCallFault fault), [], heap, Core.Module.ListHeap.empty⟩
      | .running heap .. | .delivering heap .. | .receiving heap .. =>
        ⟨space, .error .directCallFuelExhausted, [], heap, Core.Module.ListHeap.empty⟩ :=
  by
    simp [runInstructionsIn, effectWithLists, effect, invokeAdjacentKeywordDiscard, found, admitted]
    generalize (((callbackSession space context.heap).prepareCall .discard
      (.literal (.function closure)) [.literal (.int value)]).runPrefix context.table context.fuel).2.state =
      state
    cases state with
    | finished heap result => cases result <;> rfl
    | _ => rfl

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
