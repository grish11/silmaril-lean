module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms
import Silmaril.Languages.Python.Compile.ModuleEntry.Thms
public import Silmaril.Languages.Python.Core.Module.Functions.Thms
public import Silmaril.Languages.Python.Core.Text.Thms
import Silmaril.Languages.Python.Core.Text.Slice.Thms
public import Silmaril.Languages.Python.Core.Module.SeededCall.Thms
public import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Thms
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Identity
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.IntegerBuiltin
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ListConstruction
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.BoolIdentity

public section

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Core.Module.SeededCall (CallObservation Delivers Expectation Failure Namespace Raised Value)
open Core.Module.Functions (TopFunction)
open Core.Closure (Function Heap)
open Core.Module (ListHeap ListObject)
open Core.Closure.Executor (Fault labelledIn)

theorem legacyNumericIsinstanceSeed_float (placement : SeedPlacement) :
    (legacyNumericIsinstanceSeed placement).lookupGlobal "float" = some (.builtin .float) := by
  cases placement <;> rfl

theorem legacyNumericIsinstanceSeed_assertTrue (placement : SeedPlacement) :
    (legacyNumericIsinstanceSeed placement).lookupGlobal "___assertTrue" = some (.helper .assertTrue) := by
  cases placement <;> rfl

/-- Observe the exact stock instance result before the helper settles. The
class is the descriptor read from the live namespace, including any shadow. -/
theorem observeNestedCallIn_instance {space : Namespace} {context : CallContext}
    {outer inner className : String} {operand : Core.Module.Functions.Operand}
    {value : Value} {kind : Core.Module.SeededCall.Builtin} {result : Bool}
    (helper : space.lookupGlobal outer = some (.helper .assertTrue))
    (probe : space.lookupGlobal inner = some (.builtin .isinstance))
    (evaluated : (lowerCallOperand operand).eval space #v[] = .ok value)
    (classBinding : space.lookupGlobal className = some (.builtin kind))
    (tested : Core.Module.SeededCall.invoke (.builtin .isinstance) [value, .builtin kind] =
      .ok (.bool result)) :
    observeNestedCallIn space context .discard outer [.call inner [operand, .readGlobal className]] =
      (⟨if result then .ok none else .error (.raised (.assertionError (.boolean false))),
        [⟨inner, ⟨.ok (.bool result), none⟩⟩,
         ⟨outer, ⟨if result then .ok .none else .error (.raised (.assertionError (.boolean false))), none⟩⟩]⟩,
        context.heap) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.observeNestedCallIn_instance
    helper probe evaluated classBinding tested

/-- Invoke both live descriptors, recording the Boolean before the assertion helper result. -/
theorem observeNestedCallIn_intInstance {space : Namespace} {context : CallContext}
    {outer inner className : String} (value : Int)
    (helper : space.lookupGlobal outer = some (.helper .assertTrue))
    (probe : space.lookupGlobal inner = some (.builtin .isinstance))
    (classBinding : space.lookupGlobal className = some (.builtin .int)) :
    observeNestedCallIn space context .discard outer
      [.call inner [.literal (.int value), .readGlobal className]] =
      (⟨.ok none, [⟨inner, ⟨.ok (.bool true), none⟩⟩, ⟨outer, ⟨.ok .none, none⟩⟩]⟩, context.heap) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.observeNestedCallIn_intInstance
    value helper probe classBinding

/-- A failed inner preparation records the inner failure and skips the
outer invocation, including when its saved value is noncallable. -/
theorem observeNestedCallIn_innerPreparationError {space : Namespace} {context : CallContext}
    {outer inner : String} {operands : List Core.Module.Functions.Operand} {callee : Value} {error : Failure}
    (outerFound : space.lookupGlobal outer = some callee)
    (failed : Core.Module.SeededCall.resolveCall space #v[] (.global inner) (operands.map lowerCallOperand) =
      .error error) :
    observeNestedCallIn space context .discard outer [.call inner operands] =
      (⟨.error (.ofCall error), [⟨inner, ⟨.error error, none⟩⟩]⟩, context.heap) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.observeNestedCallIn_innerPreparationError
    outerFound failed

theorem intDivMod_operand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Core.Closure.Heap) (frame : Core.Closure.Frame layout)
    (op : Core.Closure.IntDivModOp) (numerator divisor : Int) :
    (lowerCallOperand (.intDivMod op numerator divisor)).eval space #v[] =
      (((Core.Module.Functions.Operand.intDivMod op numerator divisor).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.intDivMod_operand_agrees
    space globals heap frame op numerator divisor

theorem intTrueDiv_operand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Heap) (frame : Core.Closure.Frame layout)
    (numerator divisor : Int) :
    (lowerCallOperand (.intTrueDiv numerator divisor)).eval space #v[] =
      (((Core.Module.Functions.Operand.intTrueDiv numerator divisor).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.intTrueDiv_operand_agrees
    space globals heap frame numerator divisor

theorem floatDiv_operand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Heap) (frame : Core.Closure.Frame layout)
    (operands : Core.Binary64.FloatOperands) :
    (lowerCallOperand (.floatDiv operands)).eval space #v[] =
      (((Core.Module.Functions.Operand.floatDiv operands).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.floatDiv_operand_agrees
    space globals heap frame operands

theorem mixedAdd_operand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Heap) (frame : Core.Closure.Frame layout)
    (integer : Int) (floating : Silmaril.Numeric.Ieee754.F64.Finite) :
    (lowerCallOperand (.mixedAdd integer floating)).eval space #v[] =
      (((Core.Module.Functions.Operand.mixedAdd integer floating).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.mixedAdd_operand_agrees
    space globals heap frame integer floating

theorem floatAdd_operand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Heap) (frame : Core.Closure.Frame layout)
    (left right : Silmaril.Numeric.Ieee754.F64.Finite) :
    (lowerCallOperand (.floatAdd left right)).eval space #v[] =
      (((Core.Module.Functions.Operand.floatAdd left right).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.floatAdd_operand_agrees
    space globals heap frame left right

theorem floatSub_operand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Heap) (frame : Core.Closure.Frame layout)
    (operands : Core.Binary64.FloatOperands) :
    (lowerCallOperand (.floatSub operands)).eval space #v[] =
      (((Core.Module.Functions.Operand.floatSub operands).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.floatSub_operand_agrees
    space globals heap frame operands

theorem floatMul_operand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Heap) (frame : Core.Closure.Frame layout)
    (operands : Core.Binary64.FloatOperands) :
    (lowerCallOperand (.floatMul operands)).eval space #v[] =
      (((Core.Module.Functions.Operand.floatMul operands).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.floatMul_operand_agrees
    space globals heap frame operands

theorem observeArguments_iff {space : Namespace} {arguments : List Argument}
    {values : Except Failure (List Value)} {calls : List CallEvent} :
    observeArguments space arguments = (values, calls) ↔ EvaluatesArguments space arguments values calls :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.observeArguments_iff

theorem observeNestedCall_missing {space : Namespace} {destination : Core.Module.Functions.Destination}
    {name : String} {arguments : List Argument} (missing : space.lookupGlobal name = none) :
    observeNestedCall space destination name arguments = ⟨.error (.raised (.runtime (.nameError name))), []⟩ :=
  by simp [observeNestedCall, missing]

theorem observeNestedCall_failedArguments {space : Namespace} {destination : Core.Module.Functions.Destination}
    {name : String} {callee : Value} {arguments : List Argument} {error : Failure} {calls : List CallEvent}
    (found : space.lookupGlobal name = some callee)
    (failed : EvaluatesArguments space arguments (.error error) calls) :
    observeNestedCall space destination name arguments = ⟨.error (.ofCall error), calls⟩ :=
  by simp [observeNestedCall, found, observeArguments_iff.mpr failed]

theorem run_preserves_builtins {source : Source.Module} (space : Namespace) (compiled : Compiled source)
    (heap : Heap := .empty) (fuel : Nat := 1000) (lists : ListHeap := .empty) :
    (run space compiled heap fuel lists).residual.builtins = space.builtins :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.preserves_builtins
    space compiled.instructions { table := compiled.table, heap, fuel } lists

/-- The comparison profile gives identical values and defined failures when
both runners observe the same globals. -/
theorem evaluateScalar_comparable {scope : Source.Scope} (space : Namespace)
    (session : Core.Module.Functions.Session)
    (reads : ∀ name, space.lookupGlobal name = (session.globals name).map seededValue)
    (operand : Operand scope) (admitted : operand.comparable = true) :
    evaluateScalar space true operand = ((Run.evaluate session operand).map seededValue).mapError scalarFailure :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Identity.evaluateScalar_agrees
    space session reads operand admitted

theorem evaluate_singletonResult {scope : Source.Scope} (session : Core.Module.Functions.Session)
    (operand : Operand scope) (certified : operand.singletonResult = true) (value : Core.Closure.Value)
    (evaluated : Run.evaluate session operand = .ok value) :
    ∃ exact, (Run.scalar? value).bind Core.Module.Value.singleton? = some exact :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Identity.evaluate_singletonResult
    session operand certified value evaluated

theorem evaluateScalar_identityContext {scope : Source.Scope} (space : Namespace)
    (left : Operand scope) (links : List (Core.Module.IdentityOperator × Operand scope)) :
    evaluateScalar space false (.identityChain left links) = evaluateScalar space true (.identityChain left links) := by
  rw [evaluateScalar, evaluateScalar]

theorem run_identityAssertion {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (left : Operand scope) (links : List (Core.Module.IdentityOperator × Operand scope)) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.scalar (.assertion (.identityChain left links)) :: rest) =
      match (assertOperand space (.identityChain left links) true).binding with
      | .ok _ => runInstructionsIn space context rest
      | .error error => ⟨space, .error error, [], context.heap, Core.Module.ListHeap.empty⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Identity.run_identityAssertion space context left links rest

theorem evaluateScalar_conditionalResult {scope : Source.Scope} (space : Namespace)
    (equalityOperand : Bool) (operand : ModuleEntry.Operand scope) :
    evaluateScalar space equalityOperand operand.conditionalResult =
      match operand with
      | .boolean value => .ok (.bool value)
      | other => evaluateScalar space equalityOperand other := by
  cases operand with
  | boolean value => cases value <;> simp [Operand.conditionalResult, Operand.booleanResult, evaluateScalar] <;> rfl
  | _ => rfl

theorem evaluateScalar_booleanResult {scope : Source.Scope} (space : Namespace)
    (equalityOperand value : Bool) :
    evaluateScalar space equalityOperand (ModuleEntry.Operand.booleanResult (scope := scope) value) =
      .ok (.bool value) :=
  evaluateScalar_conditionalResult space equalityOperand (.boolean value)

theorem evaluateScalar_scalarResult {scope : Source.Scope} (space : Namespace) (equalityOperand : Bool)
    (value : Core.Module.Value) :
    evaluateScalar space equalityOperand (ModuleEntry.Operand.scalarResult (scope := scope) value) =
      .ok (seededValue (Run.embed value)) := by
  cases value with
  | int value => simp [Operand.scalarResult, evaluateScalar, lowerScalarOperand]; rfl
  | bool value => exact evaluateScalar_booleanResult space equalityOperand value
  | none => simp [Operand.scalarResult, evaluateScalar, lowerScalarOperand]; rfl

/-- A certified Boolean selection evaluates to the same tagged scalar in
both runners, independently of their incoming namespaces. -/
theorem evaluate_checkedBooleanOp {scope : Source.Scope} (session : Core.Module.Functions.Session)
    (space : Namespace) (context : Bool) {operator : Source.BooleanOperator} {operands : List Source.Expr}
    {value : Core.Module.Value} (checked : checkedBooleanOp? operator operands = some value) :
    (lowerOperand scope (.booleanOp operator operands)).map
        (fun operand => Run.evaluate session operand.val) = .ok (.ok (Run.embed value)) ∧
      (lowerOperand scope (.booleanOp operator operands)).map
        (fun operand => evaluateScalar space context operand.val) = .ok (.ok (seededValue (Run.embed value))) := by
  rw [lower_checkedBooleanOp checked]
  simp [Except.map, Run.evaluate_scalarResult, evaluateScalar_scalarResult]

theorem evaluate_closedSequenceComparison {scope : Source.Scope} (session : Core.Module.Functions.Session)
    (space : Namespace) (context : Bool) {left right : Source.Expr} {operator : Source.Comparison}
    {value : Bool} (checked : closedSequenceComparison? left operator right = some value) :
    (lowerOperand scope (.comparison left [(operator, right)])).map
        (fun operand => Run.evaluate session operand.val) = .ok (.ok (.bool value)) ∧
      (lowerOperand scope (.comparison left [(operator, right)])).map
        (fun operand => evaluateScalar space context operand.val) = .ok (.ok (.bool value)) := by
  rw [lower_closedSequenceComparison checked]
  simp only [Except.map, Except.ok.injEq]
  exact ⟨Run.evaluate_scalarResult session (.bool value), evaluateScalar_booleanResult space context value⟩

theorem literalBooleanEquality_call_agrees {scope : Source.Scope}
    (space : Namespace) (context left right : Bool) :
    let operand : Operand scope := .binary .equal (.boolean left) (.boolean right)
    (callOperand? operand).map (fun value => (lowerCallOperand value).eval space #v[]) =
      some (evaluateScalar space context operand) := by
  simp only [evaluateScalar]
  cases left <;> cases right <;> rfl

theorem evaluateScalar_notEqual {scope : Source.Scope} (space : Namespace) (context : Bool)
    (left right : ModuleEntry.Operand scope) :
    evaluateScalar space context (.binary .notEqual left right) = (do
      let first ← evaluateScalar space true left
      let second ← evaluateScalar space true right
      let some first := scalar? first | throw .unsupported
      let some second := scalar? second | throw .unsupported
      return .bool (!first.equal second)) := by rw [evaluateScalar]; rfl

theorem effect_scalarResultAssign {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (name : Source.Name) (reference : ModuleEntry.GlobalReference scope name) (value : Core.Module.Value) :
    effect space context (.scalar (.assign name reference (.scalarResult value))) =
      (⟨.ok (some (name, seededValue (Run.embed value))), []⟩, context.heap) := by
  simp only [effect, evaluateScalar_scalarResult]
  rfl

theorem truth_scalar {value : Core.Module.Value} : truth (seededValue (Run.embed value)) = value.truth := by
  cases value <;> rfl

theorem assertOperand_scalarResult {scope : Source.Scope} (space : Namespace) (value : Core.Module.Value)
    (expected : Bool) :
    assertOperand space (ModuleEntry.Operand.scalarResult (scope := scope) value) expected =
      ⟨if value.truth = expected then .ok none else .error (.raised (.assertionError .empty)), []⟩ := by
  simp only [assertOperand, evaluateScalar_scalarResult, Except.bind, assertTruthAs, truth_scalar]
  split <;> rfl

theorem run_scalarResultAssign {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (name : Source.Name) (reference : ModuleEntry.GlobalReference scope name) (value : Core.Module.Value)
    (rest : List (Instruction scope)) (lists : ListHeap := .empty) :
    runInstructionsIn space context (.scalar (.assign name reference (.scalarResult value)) :: rest) lists =
      runInstructionsIn (space.bindGlobal name (seededValue (Run.embed value))) context rest lists := by
  simp [runInstructionsIn, effectWithLists, effect, evaluateScalar_scalarResult]
  rfl

theorem run_scalarResultAssert {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (value : Core.Module.Value) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.scalar (.assertion (.scalarResult value)) :: rest) =
      if value.truth then runInstructionsIn space context rest
      else ⟨space, .error (.raised (.assertionError .empty)), [], context.heap, Core.Module.ListHeap.empty⟩ := by
  by_cases h : value.truth <;> simp [runInstructionsIn, effectWithLists, effect, assertOperand_scalarResult, h]

theorem effect_conditionalAssign {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (name : Source.Name) (reference : ModuleEntry.GlobalReference scope name) (selected : ModuleEntry.Operand scope) :
    effect space context (.scalar (.assign name reference selected.conditionalResult)) =
      let result : Core.Module.SeededCall.Result := match selected with
        | .boolean value => .ok (.bool value)
        | other => evaluateScalar space false other
      (⟨(result.map fun value => some (name, value)).mapError ModuleFailure.ofCall, []⟩, context.heap) := by
  simp only [effect, evaluateScalar_conditionalResult]

theorem effect_conditionalAssert {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (selected : ModuleEntry.Operand scope) :
    effect space context (.scalar (.assertion selected.conditionalResult)) =
      let result : Core.Module.SeededCall.Result := match selected with
        | .boolean value => .ok (.bool value)
        | other => evaluateScalar space false other
      let checked := result.bind (assertTruthAs true)
      (⟨(checked.map fun _ => none).mapError ModuleFailure.ofCall, []⟩, context.heap) := by
  simp only [effect, assertOperand, evaluateScalar_conditionalResult]

theorem callback_path (space : Namespace) (context : CallContext) (closure : Function) :
    let invocation := callbackInvocation space context.heap closure
    let (events, residual) := invocation.runPrefix context.table context.fuel
    (labelledIn context.table (callbackSession space context.heap).globals).Path
      invocation.state events residual.state :=
  (callbackInvocation space context.heap closure).run_path context.table context.fuel

theorem callback_delivers {space : Namespace} {expectation : Expectation}
    {heap residual : Heap} {result : Core.Closure.Result} {observation : CallObservation} :
    observeCallback space expectation (.finished heap result) = (.ok observation, residual) ↔
      let inner := (result.map seededValue).mapError (callbackError space)
      Delivers expectation inner observation.result ∧
        observation.caught = expectation.caught? inner ∧ residual = heap := by
  cases observation
  simp [observeCallback, Expectation.delivers_iff.symm, eq_comm, and_assoc]

theorem invokeCall_published {space : Namespace} {context : CallContext} {closure : Function}
    (expectation : Expectation)
    {definition : Core.Closure.Dispatch.Definition Core.Closure.Executor.Body closure.code.layout}
    (published : closure ∈ context.published)
    (resolved : Core.Closure.Dispatch.resolve context.table closure.code = .ok definition)
    (noParameters : definition.parameters.slots = []) :
    invokeCall space context (.helper (.assertRaises expectation.onReturn))
        [.exceptionClass expectation.expected, .function closure] =
      invokeCallback space context expectation closure := by
  cases expectation
  simp [invokeCall, CallContext.acceptsPublishedCall, CallContext.acceptsCallFrom, Core.Module.SeededCall.Request.decode, published, resolved,
    noParameters]

theorem callback_fault (space : Namespace) (expectation : Expectation) (heap : Heap)
    (stack : Core.Closure.Executor.Stack) (fault : Fault) :
    observeCallback space expectation (.faulted heap stack fault) = (.error (.callbackFault fault), heap) := rfl

theorem callback_seedOnlyGlobal {space : Namespace} {heap : Heap} {name : String} {value : Value}
    (found : space.lookupGlobal name = some value) (unsupported : ordinaryValue? value = none) :
    (callbackSession space heap).globals name = none ∧
      callbackError space (.nameError name) = .unsupported := by
  simp [callbackSession, callbackError, found, unsupported]

theorem failing_instruction {scope : Source.Scope} {space : Namespace} {instruction : Instruction scope}
    {rest : List (Instruction scope)} {error : ModuleFailure}
    {context : CallContext} {lists : Core.Module.ListHeap}
    (failed : (effect space context instruction lists).1.binding = .error error) :
    runInstructionsIn space context (instruction :: rest) lists =
      ⟨space, .error error, (effect space context instruction lists).1.calls,
        (effect space context instruction lists).2, (effectWithLists space context instruction lists).2⟩ := by
  cases instruction <;> simp_all [runInstructionsIn, effectWithLists, effect]

theorem observeTupleIdentityCall_missing (space : Namespace) (context : CallContext)
    (destination : Core.Module.Functions.Destination) {name : String} (test : TupleIdentity.Test)
    (missing : space.lookupGlobal name = none) :
    observeTupleIdentityCall space context destination name test =
      (⟨.error (.raised (.runtime (.nameError name))), []⟩, context.heap) := by
  simp only [observeTupleIdentityCall, Core.Module.SeededCall.Operand.eval, missing, Option.elim]
  rfl

theorem observeTupleIdentityCall_argument_failure (space : Namespace) (context : CallContext)
    (destination : Core.Module.Functions.Destination) {name : String} (test : TupleIdentity.Test)
    {callee : Value} {error : Failure} (found : space.lookupGlobal name = some callee)
    (failed : test.evaluate context.heap
      (fun name => ((Core.Module.SeededCall.Operand.global name).eval space #v[]).map ordinaryValue?)
      .unsupported = .error error) :
    observeTupleIdentityCall space context destination name test =
      (⟨.error (.ofCall error), []⟩, context.heap) := by
  have saved : (Core.Module.SeededCall.Operand.global name).eval space #v[] = .ok callee := by
    simp [Core.Module.SeededCall.Operand.eval, found]
  simp only [observeTupleIdentityCall, saved, failed]
  rfl

theorem observeTupleIdentityCall_helper (space : Namespace) (context : CallContext)
    {name : String} (test : TupleIdentity.Test) {answer : Bool}
    (found : space.lookupGlobal name = some (.helper .assertTrue))
    (evaluated : test.evaluate context.heap
      (fun name => ((Core.Module.SeededCall.Operand.global name).eval space #v[]).map ordinaryValue?)
      .unsupported = .ok answer) :
    observeTupleIdentityCall space context .discard name test =
      (acceptObservation .discard name
        (Core.Module.SeededCall.invokeObserved (.helper .assertTrue) [.bool answer]), context.heap) := by
  have saved : (Core.Module.SeededCall.Operand.global name).eval space #v[] = .ok (.helper .assertTrue) := by
    simp [Core.Module.SeededCall.Operand.eval, found]
  simp only [observeTupleIdentityCall, saved, evaluated]
  rfl

theorem invokeDescriptor_tuple_text_empty (heap : Heap) {text : Core.Text} (empty : text.points = []) :
    invokeDescriptor heap (.builtin .tuple) [.text text] = (⟨.ok (.returnedTuple []), none⟩, heap) := by
  simp [invokeDescriptor, Core.Text.singletons_empty empty, Heap.materializeFreshTuple, seededValue]

theorem invokeDescriptor_tuple_text_fresh (heap : Heap) {text first : Core.Text} {tail : List Core.Text}
    (split : text.singletons = first :: tail) :
    let items : List Core.Module.TupleDispatch.Element := .text first :: tail.map .text
    invokeDescriptor heap (.builtin .tuple) [.text text] =
      (⟨.ok (.tupleObject ⟨some heap.next, items⟩), none⟩, (heap.allocate (.tuple items)).2) := by
  simp [invokeDescriptor, split, Heap.materializeFreshTuple, Heap.allocate, seededValue]

theorem observeTupleFromListDisplay_stock (space : Namespace) (heap : Heap) (lists : ListHeap)
    (contents : List Core.Module.Value) (stock : space.lookupGlobal "tuple" = some (.builtin .tuple)) :
    let (value, reached) := heap.materializeFreshTuple (contents.map .scalar)
    observeTupleFromListDisplay space heap lists contents =
      ((⟨.ok (seededValue value), none⟩, reached), (lists.allocate contents).2) := by
  simp [observeTupleFromListDisplay, tupleBinding, stock, Core.Module.TupleDispatch.constructFromListDisplay_stock]

theorem observeTupleFromListDisplay_stock_notList (space : Namespace) (heap : Heap) (lists : ListHeap)
    (contents : List Core.Module.Value) (object : ListObject)
    (stock : space.lookupGlobal "tuple" = some (.builtin .tuple)) :
    (observeTupleFromListDisplay space heap lists contents).1.1.result ≠ .ok (.listObject object) := by
  rw [observeTupleFromListDisplay_stock space heap lists contents stock]
  cases contents <;> simp [seededValue, Heap.allocate]

theorem observeTupleFromListDisplay_mask (space : Namespace) (heap : Heap) (lists : ListHeap)
    (contents : List Core.Module.Value) (masked : space.lookupGlobal "tuple" = some .none) :
    observeTupleFromListDisplay space heap lists contents =
      ((⟨.error (.raised (.runtime .notCallable)), none⟩, heap), (lists.allocate contents).2) := by
  simp [observeTupleFromListDisplay, tupleBinding, masked,
    (Core.Module.TupleDispatch.constructFromListDisplay_mask lists contents).1, TupleChain.runtimeError?]

theorem observeListDisplayCall_missing (space : Namespace) (context : CallContext)
    (destination : Core.Module.Functions.Destination) (display : ListDisplay.Display) (lists : ListHeap)
    {name : String} (missing : space.lookupGlobal name = none) :
    observeListDisplayCall space context destination name display lists =
      ((acceptObservation destination name ⟨.error (.raised (.runtime (.nameError name))), none⟩,
        context.heap), lists) := by
  simp [observeListDisplayCall, missing]

theorem observeListDisplayCall_prepared (space : Namespace) (context : CallContext)
    (destination : Core.Module.Functions.Destination) (display : ListDisplay.Display) (lists : ListHeap)
    {name : String} {callee : Value} {contents : List Core.Module.Value}
    (resolved : space.lookupGlobal name = some callee)
    (evaluated : display.items.mapM (ListDisplay.Item.eval (readListItem space)) = .ok contents) :
    observeListDisplayCall space context destination name display lists =
      (observeRemainingCallIn space context destination name callee
        [listDisplayArgument display (lists.allocate contents).1] [], (lists.allocate contents).2) := by
  simp only [observeListDisplayCall, resolved, display.prepare_allocated _ _ _ evaluated]

theorem observeListDisplayCall_assertTrue (space : Namespace) (context : CallContext)
    (name : String) (items : List ListDisplay.Item) (lists : ListHeap) (contents : List Core.Module.Value)
    (resolved : space.lookupGlobal name = some (.helper .assertTrue))
    (evaluated : items.mapM (ListDisplay.Item.eval (readListItem space)) = .ok contents) :
    let object := (lists.allocate contents).1
    let result := if contents.isEmpty then .error (.raised (.assertionError (.listObject object))) else .ok .none
    observeListDisplayCall space context .discard name ⟨items, false⟩ lists =
      ((acceptObservation .discard name ⟨result, none⟩, context.heap), (lists.allocate contents).2) := by
  rw [observeListDisplayCall_prepared space context .discard ⟨items, false⟩ lists resolved evaluated]
  simp [observeRemainingCallIn, observeArgumentsIn, listDisplayArgument, invokeNestedTarget, invokeDescriptor,
    Core.Module.SeededCall.invokeObserved, Core.Module.SeededCall.Request.decode,
    Core.Module.SeededCall.invoke_assertTrue_listObject, Core.Module.ListHeap.allocate]

theorem observeTupleFromListDisplayCall_outer_missing (space : Namespace) (context : CallContext)
    (destination : Core.Module.Functions.Destination) (lists : ListHeap) {name : String}
    (contents : List Core.Module.Value) (remaining : List Argument) (missing : space.lookupGlobal name = none) :
    observeTupleFromListDisplayCall space context destination contents (some (name, remaining)) lists =
      ((⟨.error (.raised (.runtime (.nameError name))), []⟩, context.heap), lists) := by
  simp [observeTupleFromListDisplayCall, missing]

theorem run_literalArmBoolean {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (value : Bool) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.scalar (ModuleEntry.Action.assertion (.boolean value)).inLiteralArm :: rest) =
      if value then runInstructionsIn space context rest
      else ⟨space, .error (.raised (.assertionError .empty)), [], context.heap, Core.Module.ListHeap.empty⟩ := by
  cases value <;> simp [Action.inLiteralArm, runInstructionsIn, effectWithLists, effect, assertOperand,
    evaluateScalar, lowerScalarOperand, Core.Module.SeededCall.Operand.eval] <;> rfl

theorem readSequenceLength_ok_iff (space : Namespace) (length : Nat) (value : Int) :
    readSequenceLength space length = .ok value ↔
      space.lookupGlobal "len" = some (.builtin .len) ∧ value = Int.ofNat length :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.IntegerBuiltin.readSequenceLength_ok_iff space length value

theorem readSequenceLength_shadow (space : Namespace) (length : Nat) (value : Value)
    (found : Core.Module.SeededCall.lookupBinding space.moduleGlobals "len" = some value) :
    readSequenceLength space length = readSequenceLength { space with builtins := [] } length := by
  simp [readSequenceLength, Core.Module.SeededCall.Namespace.lookupGlobal, found]

theorem readOrdinal_ok_iff (space : Namespace) (point : UInt32) (valid : point.toNat < 0x110000) (value : Int) :
    readIntegerBuiltin space (.ordinal point valid) = .ok value ↔
      space.lookupGlobal "ord" = some (.builtin .ord) ∧ value = Int.ofNat point.toNat :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.IntegerBuiltin.readOrdinal_ok_iff space point valid value

theorem run_assertIntegerBuiltin {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (lists : ListHeap) (test : IntegerBuiltinTest scope) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.assertIntegerBuiltin test :: rest) lists =
      let result := readIntegerBuiltin space test.argument
      let receipt : CallEvent := ⟨test.argument.name, ⟨result.map .int, none⟩⟩
      match result.bind (checkIntegerBuiltinResult space test) with
      | .error error => ⟨space, .error (.ofCall error), [receipt], context.heap, lists⟩
      | .ok () =>
        let tail := runInstructionsIn space context rest lists
        { tail with calls := receipt :: tail.calls } :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.IntegerBuiltin.run_assertIntegerBuiltin
    space context lists test rest

theorem run_assertSequenceLength {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (test : SequenceLengthTest scope) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.assertSequenceLength test :: rest) =
      let result := readSequenceLength space test.length
      let receipt : CallEvent := ⟨"len", ⟨result.map .int, none⟩⟩
      match result.bind (checkSequenceLengthResult space test) with
      | .error error => ⟨space, .error (.ofCall error), [receipt], context.heap, Core.Module.ListHeap.empty⟩
      | .ok () =>
        let tail := runInstructionsIn space context rest
        { tail with calls := receipt :: tail.calls } :=
  run_assertIntegerBuiltin space context .empty test.toIntegerBuiltin rest

theorem constructList_ok_iff (space : Namespace) (heap : ListHeap) (argument : ListConstructorArgument)
    (object : ListObject) (updated : ListHeap) :
    constructList space heap argument = (.ok object, updated) ↔
      space.lookupGlobal "list" = some (.builtin .list) ∧
        let (contents, reached) := prepareListArgument heap argument
        reached.allocate contents = (object, updated) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ListConstruction.constructList_ok_iff
    space heap argument object updated

theorem readBoolCall_missing {scope : Source.Scope} (space : Namespace)
    (argument : Option (Operand scope)) (missing : space.lookupGlobal "bool" = none) :
    readBoolCall space argument = .error (.raised (.runtime (.nameError "bool"))) := by
  simp [readBoolCall, missing]

theorem readBoolCall_argument_error {scope : Source.Scope} (space : Namespace)
    (argument : Option (Operand scope)) (callee : Value) (error : Failure)
    (found : space.lookupGlobal "bool" = some callee)
    (failed : argument.mapM (evaluateScalar space true) = .error error) :
    readBoolCall space argument = .error error := by
  simp [readBoolCall, found, failed, Except.bind]

theorem readBoolCall_stock {scope : Source.Scope} (space : Namespace)
    (argument : Option (Operand scope)) (value : Option Value)
    (found : space.lookupGlobal "bool" = some (.builtin .bool))
    (prepared : argument.mapM (evaluateScalar space true) = .ok value) :
    readBoolCall space argument = (match scalar? (value.getD .none) with
      | some scalar => .ok scalar.truth
      | none => .error .unsupported) := by
  simp [readBoolCall, found, prepared, Except.bind]
  cases scalar? (value.getD .none) <;> rfl

theorem run_assertBoolIdentity {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (lists : ListHeap) (test : BoolIdentityTest scope) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.assertBoolIdentity test :: rest) lists =
      let result := readBoolCall space test.argument
      let receipt : CallEvent := ⟨"bool", ⟨result.map .bool, none⟩⟩
      match result.bind (checkBoolIdentityResult space test) with
      | .error error => ⟨space, .error (.ofCall error), [receipt], context.heap, lists⟩
      | .ok () =>
        let tail := runInstructionsIn space context rest lists
        { tail with calls := receipt :: tail.calls } :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.BoolIdentity.run_assertBoolIdentity
    space context lists test rest

theorem constructList_shadow (space : Namespace) (heap : ListHeap) (argument : ListConstructorArgument)
    (value : Value) (found : Core.Module.SeededCall.lookupBinding space.moduleGlobals "list" = some value) :
    constructList space heap argument = constructList { space with builtins := [] } heap argument := by
  simp [constructList, Core.Module.SeededCall.Namespace.lookupGlobal, found]

theorem constructList_missing (space : Namespace) (heap : ListHeap) (argument : ListConstructorArgument)
    (missing : space.lookupGlobal "list" = none) :
    constructList space heap argument = (.error (.raised (.runtime (.nameError "list"))), heap) := by
  simp [constructList, missing]

theorem run_assertListConstruction {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (lists : ListHeap) (test : ListConstructionTest scope) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.assertListConstruction test :: rest) lists =
      let outcome := evaluateListConstruction space lists test
      match outcome.checked with
      | .error error => ⟨space, .error (.ofCall error), [outcome.receipt], context.heap, outcome.lists⟩
      | .ok () =>
        let tail := runInstructionsIn space context rest outcome.lists
        { tail with calls := outcome.receipt :: tail.calls } :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ListConstruction.run_assertListConstruction
    space context lists test rest

theorem tupleBinding_shadow (space : Namespace) (value : Value)
    (found : Core.Module.SeededCall.lookupBinding space.moduleGlobals "tuple" = some value) :
    tupleBinding space = tupleBinding { space with builtins := [] } := by
  simp [tupleBinding, Core.Module.SeededCall.Namespace.lookupGlobal, found]

theorem checkTupleChain_corresponds {scope : Source.Scope} (space : Namespace)
    (session : Core.Module.Functions.Session) (test : TupleChainTest scope)
    (lookup : tupleLookup space = Run.tupleLookup session) :
    checkTupleChain space test = (Run.checkTupleChain session test).mapError (fun
      | .assertionError => .raised (.assertionError .empty)
      | .raised error => .raised (.runtime error)
      | _ => .unsupported) := by
  simp only [checkTupleChain, lookup, Run.checkTupleChain]
  cases (TupleChain.evaluate (Run.tupleLookup session) test).result with
  | ok value => cases value <;> rfl
  | error failure => cases failure <;> rfl

theorem run_assertTupleChain {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (lists : ListHeap) (test : TupleChainTest scope) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.assertTupleChain test :: rest) lists =
      match checkTupleChain space test with
      | .error error => ⟨space, .error (.ofCall error), [], context.heap, lists⟩
      | .ok () => runInstructionsIn space context rest lists := by
  simp only [runInstructionsIn, effectWithLists, effect]
  cases checkTupleChain space test with | error _ => rfl | ok value => cases value; rfl

/-- Settle one direct discard call from the actual executor state. A
finished call emits one receipt before its tail, and a failed call skips the tail. -/
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
        ⟨space, .error .directCallFuelExhausted, [], heap, Core.Module.ListHeap.empty⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.run_directDiscard found admitted

theorem run_directDiscard_unsupported {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {closure : Function} {rest : List (Instruction scope)}
    (found : space.lookupGlobal name = some (.function closure))
    (rejected : context.acceptsPublishedCall closure = false) :
    runInstructionsIn space context (.call .discard name [] :: rest) =
      ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], context.heap, Core.Module.ListHeap.empty⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.run_directDiscard_unsupported found rejected

theorem run_publication {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {function : TopFunction} {rest : List (Instruction scope)}
    {definition : Core.Closure.Dispatch.Definition Core.Closure.Executor.Body function.ref.layout}
    (resolved : Core.Closure.Dispatch.resolve context.table function.ref = .ok definition) :
    runInstructionsIn space context (.publish name function :: rest) =
      runInstructionsIn (space.bindGlobal name (.function function.closure))
        { context with published := function.closure :: context.published } rest :=
  by simp [runInstructionsIn, effectWithLists, effect, resolved, Except.map, Except.mapError]

theorem run_publication_fault {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {function : TopFunction} {rest : List (Instruction scope)} {error : Core.Closure.Dispatch.Failure}
    (failed : Core.Closure.Dispatch.resolve context.table function.ref = .error error) :
    runInstructionsIn space context (.publish name function :: rest) =
      ⟨space, .error (.publicationFault error), [], context.heap, Core.Module.ListHeap.empty⟩ :=
  by simp [runInstructionsIn, effectWithLists, effect, failed, Except.map, Except.mapError]

theorem tupleOperand_read_failure {space : Namespace} {items : List Core.Closure.GlobalTupleItem}
    {error : Failure} (failed : items.mapM (Core.Module.SeededCall.readTupleItem space) = .error error) :
    (Core.Module.SeededCall.Operand.tuple items).eval space #v[] = .error error := by
  simp [Core.Module.SeededCall.Operand.eval, Core.Module.SeededCall.evalTupleContents,
    Core.Closure.assembleFlatTuple, failed, Except.bind, Except.map]

theorem invokeFlatCall_tuple_reference (space : Namespace) (context : CallContext)
    (destination : Core.Module.Functions.Destination) (descriptor : Core.Module.TupleDispatch.Object) :
    invokeFlatCall space context destination (.builtin .tuple) [.tupleObject descriptor] =
      (.ok ⟨.ok (.tupleObject descriptor), none⟩, context.heap) := by
  cases destination <;> simp [invokeFlatCall, invokeCall, invokeDescriptor, Core.Module.SeededCall.Request.decode,
    Core.Module.SeededCall.invokeObserved, Core.Module.SeededCall.invoke_tuple_reference]

theorem run_textSliceGuard {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (test : TextSlice.Guard) (rest : List (Instruction scope)) (lists : ListHeap) :
    runInstructionsIn space context (.textSliceGuard test :: rest) lists =
      match checkTextSliceGuard space test with
      | .ok () => runInstructionsIn space context rest lists
      | .error error => ⟨space, .error (.ofCall error), [], context.heap, lists⟩ := by
  cases checked : checkTextSliceGuard space test <;>
    simp [runInstructionsIn, effectWithLists, effect, checked, Except.map, Except.mapError]

theorem run_bindText {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (name : Source.Name) (value : Core.Text) (rest : List (Instruction scope)) (lists : ListHeap) :
    runInstructionsIn space context (.bindText name value :: rest) lists =
      runInstructionsIn (space.bindGlobal name (.text value)) context rest lists := rfl

theorem run_readAssign {scope : Source.Scope} (space : Namespace) (context : CallContext)
    {name source : Source.Name} (target : GlobalReference scope name) (reference : GlobalReference scope source)
    (rest : List (Instruction scope)) (lists : ListHeap) :
    runInstructionsIn space context (.scalar (.assign name target (.read source reference)) :: rest) lists =
      match space.lookupGlobal source with
      | some value => runInstructionsIn (space.bindGlobal name value) context rest lists
      | none => ⟨space, .error (.raised (.runtime (.nameError source))), [], context.heap, lists⟩ := by
  cases found : space.lookupGlobal source <;>
    simp [runInstructionsIn, effectWithLists, effect, evaluateScalar, lowerScalarOperand,
      Core.Module.SeededCall.Operand.eval, found, Except.map, Except.mapError, ModuleFailure.ofCall]

theorem run_bindTuple_ok {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {items : List Core.Closure.GlobalTupleItem} {trackClosed : Bool} {values : List Core.Module.TupleDispatch.Element}
    {rest : List (Instruction scope)} {lists : ListHeap}
    (evaluated : Core.Module.SeededCall.evalTupleContents space items = .ok values) :
    let (value, heap) := context.heap.materializeModuleTuple items values trackClosed
    runInstructionsIn space context (.bindTuple name items trackClosed :: rest) lists =
      runInstructionsIn (space.bindGlobal name (seededValue value)) { context with heap := heap } rest lists := by
  simp [runInstructionsIn, effectWithLists, effect, evaluated]

theorem run_bindTuple_failure {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {items : List Core.Closure.GlobalTupleItem} {trackClosed : Bool} {error : Failure}
    {rest : List (Instruction scope)} {lists : ListHeap}
    (failed : Core.Module.SeededCall.evalTupleContents space items = .error error) :
    runInstructionsIn space context (.bindTuple name items trackClosed :: rest) lists =
      ⟨space, .error (.ofCall error), [], context.heap, lists⟩ := by
  simp [runInstructionsIn, effectWithLists, effect, failed]

theorem assertNot_operand_failure {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {operand : ModuleEntry.Operand scope} {error : Failure}
    (failed : evaluateScalar space false operand = .error error) :
    effect space context (.assertNot operand) = (⟨.error (.ofCall error), []⟩, context.heap) :=
  by simp [effect, assertOperand, failed, Except.bind, Except.map, Except.mapError]

theorem effect_assertVarNames {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (receiver : String) (needle : List UInt32) :
    effect space context (.assertVarNames receiver needle : Instruction scope) =
      (⟨(checkVarNames space context.table receiver needle).map fun _ => none, []⟩, context.heap) := rfl

/-- The guarded call follows the ordinary executor state. A settled
call contributes one receipt, with heap and tail behavior from that state. -/
theorem factoryOperands_iff {values : List Value} {operands : List Core.Module.Functions.Operand} :
    factoryOperands values = some operands ↔
      ∃ integers : List Int, integers.length ≤ 3 ∧ values = integers.map .int ∧
        operands = integers.map (fun value => .literal (.int value)) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.factoryOperands_iff

theorem acceptsFactory_escaped {context : CallContext} {closure : Function} {arity : Nat}
    {definition : Core.Closure.Dispatch.Definition Core.Closure.Executor.Body closure.code.layout}
    (recorded : closure ∈ context.escaped)
    (resolved : Core.Closure.Dispatch.resolve context.table closure.code = .ok definition)
    (slots : definition.parameters.slots.length = arity)
    (shape : factoryCode context.table closure.code 2 = true) :
    context.acceptsFactory closure arity = true := by
  have known : closure ∈ context.published ++ context.escaped := List.mem_append_right _ recorded
  simp [CallContext.acceptsFactory, CallContext.acceptsCallFrom, known, resolved, slots, shape]

theorem acceptsFactory_returnClosure {context : CallContext} {closure : Function} {arity : Nat}
    {definition : Core.Closure.Dispatch.Definition Core.Closure.Executor.Body closure.code.layout}
    {ref : Core.Closure.CodeRef} {captures : Fin ref.layout.captures → Core.Closure.CaptureSlot closure.code.layout}
    (recorded : closure ∈ context.published ++ context.escaped)
    (resolved : Core.Closure.Dispatch.resolve context.table closure.code = .ok definition)
    (slots : definition.parameters.slots.length = arity)
    (body : definition.body = .ret (.closure ref captures)) :
    context.acceptsFactory closure arity = true := by
  simp [CallContext.acceptsFactory, CallContext.acceptsCallFrom, recorded, resolved, slots,
    factoryCode, body, returnsClosure]

theorem acceptsFactory_returnClosureCall {context : CallContext} {closure : Function} {arity : Nat}
    {definition : Core.Closure.Dispatch.Definition Core.Closure.Executor.Body closure.code.layout}
    {ref : Core.Closure.CodeRef} {captures : Fin ref.layout.captures → Core.Closure.CaptureSlot closure.code.layout}
    {arguments : List (Core.Closure.Executor.Operand closure.code.layout)}
    (recorded : closure ∈ context.published ++ context.escaped)
    (resolved : Core.Closure.Dispatch.resolve context.table closure.code = .ok definition)
    (slots : definition.parameters.slots.length = arity)
    (body : definition.body = .returnCall (.closure ref captures) arguments)
    (bounded : arguments.length ≤ 1) (child : factoryCode context.table ref 1 = true) :
    context.acceptsFactory closure arity = true := by
  simpa [CallContext.acceptsFactory, CallContext.acceptsCallFrom, recorded, resolved, slots,
    factoryCode, body, returnsClosure, bounded] using child

theorem run_factory_unrecorded {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name target : String} {closure : Function} {arguments : List Core.Module.Functions.Operand}
    {values : List Value} {rest : List (Instruction scope)}
    (resolved : Core.Module.SeededCall.resolveCall space #v[] (.global name)
      (arguments.map lowerCallOperand) = .ok (.function closure, values))
    (unpublished : closure ∉ context.published) (unescaped : closure ∉ context.escaped) :
    runInstructionsIn space context (.call (.bindGlobal target) name arguments :: rest) =
      ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], context.heap, Core.Module.ListHeap.empty⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.run_factory_unrecorded resolved unpublished unescaped

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
        ⟨space, .error .directCallFuelExhausted, [], heap, Core.Module.ListHeap.empty⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.run_factory resolved profile admitted

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
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.run_adjacentKeywordDiscard found admitted

theorem observeArgumentIn_published {space : Namespace} {context : CallContext}
    {name : String} {closure : Function}
    (found : space.lookupGlobal name = some (.function closure))
    (admitted : context.acceptsPublishedCall closure = true) :
    observeArgumentIn space context (.call name []) =
      let invocation := callbackInvocation space context.heap closure
      match observeDirectCall space (invocation.runPrefix context.table context.fuel).2.state with
      | (.ok observed, heap) => (observed.result.mapError .ofCall, [⟨name, observed⟩], heap)
      | (.error error, heap) => (.error error, [], heap) := by
  have recorded : closure ∈ context.published := by
    by_contra absent
    simp [CallContext.acceptsPublishedCall, CallContext.acceptsCallFrom, absent] at admitted
  simp [observeArgumentIn, argumentObservation, invokeArgumentIn, invokePublishedArgument,
    Core.Module.SeededCall.resolveCall, Core.Module.SeededCall.Operand.eval,
    Core.Module.SeededCall.Operand.evalList, Except.bind, Except.map, found, admitted, recorded,
    factoryOperands, ordinaryCall, callbackInvocation]
  rfl

theorem observeArgumentIn_escaped {space : Namespace} {context : CallContext}
    {name : String} {closure : Function} {value : Int} {arguments : List Core.Module.Functions.Operand}
    (resolved : Core.Module.SeededCall.resolveCall space #v[] (.global name)
      (arguments.map lowerCallOperand) = .ok (.function closure, [.int value]))
    (admitted : context.acceptsEscapedArgument closure = true) :
    observeArgumentIn space context (.call name arguments) true =
      match observeDirectCall space (ordinaryCall space context closure [.literal (.int value)]) with
      | (.ok observed, heap) => (observed.result.mapError .ofCall, [⟨name, observed⟩], heap)
      | (.error error, heap) => (.error error, [], heap) := by
  simp [observeArgumentIn, resolved, invokeArgumentIn, admitted, argumentObservation]
  rfl

theorem observeArgumentIn_escapedZero {space : Namespace} {context : CallContext}
    {name : String} {closure : Function}
    (found : space.lookupGlobal name = some (.function closure))
    (admitted : context.acceptsEscapedArgument closure 0 = true) :
    observeArgumentIn space context (.call name []) true =
      match observeDirectCall space (ordinaryCall space context closure []) with
      | (.ok observed, heap) => (observed.result.mapError .ofCall, [⟨name, observed⟩], heap)
      | (.error error, heap) => (.error error, [], heap) := by
  simp [observeArgumentIn, argumentObservation, invokeArgumentIn, Core.Module.SeededCall.resolveCall, Core.Module.SeededCall.Operand.eval,
    Core.Module.SeededCall.Operand.evalList, Except.bind, Except.map, found,
    admitted]
  rfl

theorem invokePublishedArgument_admitted {space : Namespace} {context : CallContext}
    {closure : Function} {operands : List Core.Module.Functions.Operand} {values : List Value}
    (published : closure ∈ context.published) (bounded : factoryOperands values = some operands) :
    invokePublishedArgument space context closure values =
      observeDirectCall space (ordinaryCall space context closure operands) := by
  simp [invokePublishedArgument, published, bounded]

theorem invokePublishedArgument_unrecorded (space : Namespace) (context : CallContext)
    (closure : Function) (values : List Value) (unrecorded : closure ∉ context.published) :
    invokePublishedArgument space context closure values =
      (.ok ⟨.error .unsupported, none⟩, context.heap) := by
  simp [invokePublishedArgument, unrecorded]

theorem observeArgumentIn_resolutionFailure {space : Namespace} {context : CallContext}
    {allowClosureCalls : Bool} {name : String} {arguments : List Core.Module.Functions.Operand}
    {error : Failure}
    (failed : Core.Module.SeededCall.resolveCall space #v[] (.global name)
      (arguments.map lowerCallOperand) = .error error) :
    observeArgumentIn space context (.call name arguments) allowClosureCalls =
      (.error (.ofCall error), [⟨name, ⟨.error error, none⟩⟩], context.heap) := by
  simp [observeArgumentIn, failed, argumentObservation, Except.mapError]

theorem textSliceOperand_agrees {layout : Core.Closure.Layout} (space : Namespace)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Heap) (frame : Core.Closure.Frame layout)
    (receiver : Core.Text) (bounds : Core.SliceBounds) :
    (lowerCallOperand (.textSlice receiver bounds)).eval space #v[] =
      (((Core.Module.Functions.Operand.textSlice receiver bounds).lower.evalIn globals heap frame).map
        seededValue).mapError (fun
          | .defined error => .raised (.runtime error)
          | _ => .unsupported) := by
  cases sliced : receiver.slice? bounds <;>
    simp [lowerCallOperand, Core.Module.SeededCall.Operand.eval, Core.Module.Functions.Operand.lower,
      Core.Closure.Executor.Operand.evalIn, sliced, Except.map, Except.mapError, seededValue]

theorem observeArgumentIn_textSlice {space : Namespace} {context : CallContext}
    {receiver result : Core.Text} {bounds : Core.SliceBounds} (allowEscaped : Bool)
    (sliced : receiver.slice? bounds = some result) :
    observeArgumentIn space context (.scalar (.textSlice receiver bounds)) allowEscaped =
      (.ok (.text result), [], context.heap) := by
  simp [observeArgumentIn, lowerCallOperand, Core.Module.SeededCall.Operand.eval, sliced, Except.mapError]

theorem observeArgumentIn_textSlice_zero {space : Namespace} {context : CallContext}
    (receiver : Core.Text) {bounds : Core.SliceBounds} (allowEscaped : Bool) (zero : bounds.step = some 0) :
    observeArgumentIn space context (.scalar (.textSlice receiver bounds)) allowEscaped =
      (.error (.raised (.runtime .zeroSliceStep)), [], context.heap) := by
  simp [observeArgumentIn, lowerCallOperand, Core.Module.SeededCall.Operand.eval,
    Core.Text.slice_zero receiver bounds zero, Except.mapError, ModuleFailure.ofCall]

theorem argumentObservation_tuple (space : Namespace) (name : String) (heap : Heap)
    (items : List Core.Module.TupleDispatch.Element) :
    argumentObservation name (observeDirectCall space (.finished heap (.ok (.tuple items)))) =
      (.ok (.returnedTuple items), [⟨name, ⟨.ok (.returnedTuple items), none⟩⟩], heap) := rfl

theorem argumentObservation_fault (space : Namespace) (name : String) (heap : Heap)
    (stack : Core.Closure.Executor.Stack) (fault : Fault) :
    argumentObservation name (observeDirectCall space (.faulted heap stack fault)) =
      (.error (.directCallFault fault), [], heap) := rfl

theorem observeArgumentsIn_stop {space : Namespace} {context : CallContext} {allowEscaped : Bool}
    {argument : Argument} {rest : List Argument} {error : ModuleFailure} {calls : List CallEvent} {heap : Heap}
    (failed : observeArgumentIn space context argument allowEscaped = (.error error, calls, heap)) :
    observeArgumentsIn space context (argument :: rest) allowEscaped = (.error error, calls, heap) := by
  simp [observeArgumentsIn, failed]

theorem observeArgumentsIn_next {space : Namespace} {context : CallContext} {allowEscaped : Bool}
    {argument : Argument} {rest : List Argument} {value : Value} {calls : List CallEvent} {heap : Heap}
    (first : observeArgumentIn space context argument allowEscaped = (.ok value, calls, heap)) :
    observeArgumentsIn space context (argument :: rest) allowEscaped =
      let (values, later, residual) := observeArgumentsIn space { context with heap } rest allowEscaped
      (values.map (value :: ·), calls ++ later, residual) := by
  simp [observeArgumentsIn, first]

theorem observeNestedCallIn_missing {space : Namespace} {context : CallContext}
    {destination : Core.Module.Functions.Destination} {name : String} {arguments : List Argument}
    (missing : space.lookupGlobal name = none) :
    observeNestedCallIn space context destination name arguments =
      (⟨.error (.raised (.runtime (.nameError name))), []⟩, context.heap) := by
  simp [observeNestedCallIn, missing]

theorem observeNestedCallIn_failedArguments {space : Namespace} {context : CallContext}
    {destination : Core.Module.Functions.Destination} {name : String} {callee : Value}
    {arguments : List Argument} {error : ModuleFailure} {calls : List CallEvent} {heap : Heap}
    (found : space.lookupGlobal name = some callee)
    (failed : observeArgumentsIn space context arguments (allowsEscapedArgument destination callee) =
      (.error error, calls, heap)) :
    observeNestedCallIn space context destination name arguments = (⟨.error error, calls⟩, heap) := by
  simp [observeNestedCallIn, observeRemainingCallIn, found, failed]

theorem observeNestedCallIn_settledArguments {space : Namespace} {context : CallContext}
    {destination : Core.Module.Functions.Destination} {name : String} {callee : Value}
    {arguments : List Argument} {values : List Value} {calls : List CallEvent} {heap : Heap}
    (found : space.lookupGlobal name = some callee)
    (evaluated : observeArgumentsIn space context arguments (allowsEscapedArgument destination callee) =
      (.ok values, calls, heap)) :
    observeNestedCallIn space context destination name arguments =
      match invokeNestedTarget space { context with heap } callee values with
      | (.ok result, residual) =>
        let outer := acceptObservation destination name result
        ({ outer with calls := calls ++ outer.calls }, residual)
      | (.error error, residual) => (⟨.error error, calls⟩, residual) := by
  simp [observeNestedCallIn, observeRemainingCallIn, found, evaluated]
  rfl

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
