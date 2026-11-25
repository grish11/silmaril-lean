module

import Silmaril.Languages.Python.Core.Closure.Finite.Executor.Thms
import Silmaril.Languages.Python.Core.Closure.Executor.Thms
meta import Silmaril.Languages.Python.Core.Closure.Finite.Executor.Defs
meta import Silmaril.Languages.Python.Core.Closure.Finite.Dispatch.Defs
meta import Silmaril.Languages.Python.Core.Closure.Finite.Defs
meta import Silmaril.Languages.Python.Core.Closure.Executor.Defs
meta import Silmaril.Languages.Python.Core.Closure.Dispatch.Defs
meta import Silmaril.Languages.Python.Core.Closure.Call.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Mathlib.Data.List.AList

namespace Silmaril.Languages.Python.Core.Closure.Finite.Executor

private abbrev callerLayout : Layout := ⟨1, 1, 0⟩
private abbrev calleeLayout : Layout := ⟨2, 0, 1⟩
private def output : Slot callerLayout := .local 0
private def rest : Closure.Executor.Body callerLayout := .ret (.read output)
private def heap : HeapTable := HeapTable.empty.reserve 1
private def frame : Frame callerLayout :=
  ⟨fun _ => none, fun _ => ⟨0⟩, Fin.elim0⟩
private def caller : Call.Saved Closure.Executor.Continuation :=
  ⟨callerLayout, frame, ⟨output, rest⟩⟩
private abbrev olderLayout : Layout := ⟨1, 0, 0⟩
private def older : Call.Saved Closure.Executor.Continuation :=
  ⟨olderLayout, ⟨fun _ => none, Fin.elim0, Fin.elim0⟩, ⟨.local 0, .ret (.read (.local 0))⟩⟩
private def ref : CodeRef := ⟨17, calleeLayout⟩

private def code (result : Closure.Executor.Operand calleeLayout) : CodeRows :=
  (∅ : CodeRows).insert ref.key
    ⟨calleeLayout, ⟨⟨[.local 0], by decide⟩, .store (.capture 0) (.read (.local 0)) (.ret result)⟩⟩

private def start : State :=
  .running ⟨heap, frame⟩ (.call output (.closure ref (fun _ => .owned 0)) [.literal (.int 7)] rest) [older]

#guard
  match runPrefix (code (.read (.capture 0))) 12 start with
  | ([.enter _, .resume (.ok (.int 7)), .resume (.ok (.int 7)), .complete (.ok (.int 7))],
      .finished residual (.ok (.int 7))) =>
      match residual.rows.lookup 0 with
      | some (.int 7) => true
      | _ => false
  | _ => false

#guard
  match runPrefix (code (.read (.local 1))) 12 start with
  | ([.enter _, .resume (.error (.unboundLocal 1)), .resume (.error (.unboundLocal 1)),
        .complete (.error (.unboundLocal 1))], .finished residual (.error (.unboundLocal 1))) =>
      match residual.rows.lookup 0 with
      | some (.int 7) => true
      | _ => false
  | _ => false

example : advance (∅ : CodeRows) start =
    some (some (.fault (.missingCode 17)), .faulted heap [older] (.missingCode 17)) := rfl

private def residual : HeapTable := heap.bind ⟨0⟩ (.int 7) (by decide)
private def result : Result := .error (.unboundLocal 1)
private def table : CodeRows := code (.read (.local 1))
private def deliver : State := .delivering residual [caller, older] result
private def receive : Closure.Executor.State := .receiving residual.project caller [older] result
private def propagate : Closure.Executor.State := .delivering residual.project [older] result

private theorem deliveryRun :
    (semantic table.project).Execution deliver.project [some (.resume result), none]
      propagate [deliver.project, receive, propagate] :=
  .stepL (Closure.Executor.StepIn.resume _ caller [older] result)
    (.stepL (Closure.Executor.StepIn.receiveError _ caller [older] (.unboundLocal 1)) (.refl _))

example : ∃ final states,
    (presented table).Execution deliver [some (.resume result), none] final states ∧
      states.map State.project = [deliver.project, receive, propagate] ∧ final.project = propagate :=
  execution_readback deliveryRun

private def globals : Closure.Executor.GlobalLookup := fun name =>
  if name = "argument" then some (.int 11) else none

private def startGlobal : State :=
  .running ⟨heap, frame⟩
    (.call output (.closure ref (fun _ => .owned 0)) [.readGlobal "argument"] rest) []

#guard
  match runPrefixIn (code (.read (.capture 0))) globals 12 startGlobal with
  | ([.enter _, .resume (.ok (.int 11)), .complete (.ok (.int 11))], .finished residual (.ok (.int 11))) =>
    match residual.rows.lookup 0 with
    | some (.int 11) => true
    | _ => false
  | _ => false

example : advanceIn table Closure.Executor.emptyGlobals startGlobal =
    some (none, .delivering heap [] (.error (.nameError "argument"))) := rfl

example (value : Bool) : advanceIn table globals
    (.running ⟨heap, frame⟩ (.call output (.literal (.bool value)) [] rest) [older]) =
    some (none, .delivering heap [older] (.error .notCallable)) := rfl

private def returning (value : Value) : State :=
  .running (layout := calleeLayout)
    ⟨residual, ⟨fun _ => none, Fin.elim0, fun _ => ⟨0⟩⟩⟩ (.ret (.literal value)) [caller]

private def returned (value : Value) : Closure.Executor.State :=
  .delivering residual.project [caller] (.ok value)

private def resumed (value : Value) : Closure.Executor.State :=
  .receiving residual.project caller [] (.ok value)

private def stored (value : Value) : Closure.Executor.State :=
  let updated : Frame callerLayout := { frame with
    locals := fun slot => if slot = 0 then some value else frame.locals slot }
  .running residual.project updated rest []

private def delivered (value : Value) : Closure.Executor.State :=
  .delivering residual.project [] (.ok value)

private def completed (value : Value) : Closure.Executor.State :=
  .finished residual.project (.ok value)

private theorem returnedRun (value : Value) :
    (semanticIn table.project globals).Execution (returning value).project
      [none, some (.resume (.ok value)), none, none, some (.complete (.ok value))] (completed value)
      [(returning value).project, returned value, resumed value, stored value, delivered value, completed value] := by
  refine .stepL (.ret (.literal value)) (.stepL (.resume _ caller [] (.ok value)) ?_)
  refine .stepL (.receive (.ok ?_)) (.stepL (.ret (.read output)) (.stepL (.complete _ _) (.refl _)))
  rfl

private theorem returnReadback (value : Value) :
    ∃ final states, (presentedIn table globals).Execution (returning value)
      [none, some (.resume (.ok value)), none, none, some (.complete (.ok value))] final states ∧
      states.map State.project =
        [(returning value).project, returned value, resumed value, stored value, delivered value, completed value] ∧
      final.project = completed value ∧ final.completion? = some (.ok value) := by
  obtain ⟨final, states, run, stateEq, finalEq⟩ := executionIn_readback (returnedRun value)
  have observed : Closure.Executor.observes final.project (.ok value) := by
    rw [finalEq]
    rfl
  exact ⟨final, states, run, stateEq, finalEq, (observes_iff final _).mp observed⟩

example :
    ∃ final states, (presentedIn table globals).Execution (returning Value.none)
      [none, some (.resume (.ok .none)), none, none, some (.complete (.ok .none))] final states ∧
      states.map State.project = [(returning Value.none).project, returned Value.none,
        resumed Value.none, stored Value.none, delivered Value.none, completed Value.none] ∧
      final.project = completed Value.none ∧ final.completion? = some (.ok .none) :=
  returnReadback Value.none

#guard
  match runPrefixIn table globals 5 (returning Value.none) with
  | ([.resume (.ok .none), .complete (.ok .none)], .finished finalHeap (.ok .none)) =>
    match finalHeap.rows.lookup 0 with
    | some (.int 7) => finalHeap.next == 1
    | _ => false
  | _ => false

private def ownedOutput : Slot callerLayout := .owned 0

private def assertionCaller : Call.Saved Closure.Executor.Continuation :=
  ⟨callerLayout, frame, ⟨ownedOutput, .ret (.read ownedOutput)⟩⟩

private def assertionEnvironment : Snapshot calleeLayout :=
  ⟨residual, ⟨fun _ => none, Fin.elim0, fun _ => ⟨0⟩⟩⟩

private def assertionTail : Closure.Executor.Body calleeLayout :=
  .store (.capture 0) (.literal (.int 23)) (.ret (.literal (.int 5)))

-- The callee has already updated cell 0. Its tail and the caller's result
-- destination would both overwrite that cell if the assertion continued.
private def asserting (test : Closure.Executor.Operand calleeLayout) : State :=
  .running assertionEnvironment (.assert test assertionTail) [assertionCaller]

private def assertionFailure : Result := .error .assertionError

private theorem failingAssertionRun :
    (semanticIn table.project globals).Execution (asserting (.literal .none)).project
      [none, some (.resume assertionFailure), none, some (.complete assertionFailure)]
      (.finished residual.project assertionFailure)
      [(asserting (.literal .none)).project, .delivering residual.project [assertionCaller] assertionFailure,
        .receiving residual.project assertionCaller [] assertionFailure,
        .delivering residual.project [] assertionFailure, .finished residual.project assertionFailure] :=
  .stepL (.assertFalse (.literal .none) rfl)
    (.stepL (.resume _ _ _ _) (.stepL (.receiveError _ _ _ _) (.stepL (.complete _ _) (.refl _))))

example : ∃ final states, (presentedIn table globals).Execution (asserting (.literal .none))
      [none, some (.resume assertionFailure), none, some (.complete assertionFailure)] final states ∧
    states.map State.project = [(asserting (.literal .none)).project,
      .delivering residual.project [assertionCaller] assertionFailure,
      .receiving residual.project assertionCaller [] assertionFailure,
      .delivering residual.project [] assertionFailure, .finished residual.project assertionFailure] ∧
    final.project = .finished residual.project assertionFailure ∧ final.completion? = some assertionFailure := by
  obtain ⟨final, states, run, stateEq, finalEq⟩ := executionIn_readback failingAssertionRun
  have observed : Closure.Executor.observes final.project assertionFailure := by
    rw [finalEq]
    rfl
  exact ⟨final, states, run, stateEq, finalEq, (observes_iff final _).mp observed⟩

#guard
  match runPrefixIn table globals 4 (asserting (.literal .none)),
      runPrefixIn table globals 7 (asserting (.literal (.int (-1)))) with
  | ([.resume (.error .assertionError), .complete (.error .assertionError)],
      .finished failedHeap (.error .assertionError)),
    ([.resume (.ok (.int 5)), .complete (.ok (.int 5))], .finished passedHeap (.ok (.int 5))) =>
    match failedHeap.rows.lookup 0, passedHeap.rows.lookup 0 with
    | some (.int 7), some (.int 5) => failedHeap.next == 1 && passedHeap.next == 1
    | _, _ => false
  | _, _ => false

example : advanceIn table globals (asserting (.readGlobal "missing")) =
    some (none, .delivering residual [assertionCaller] (.error (.nameError "missing"))) := rfl

example : advanceIn table (fun _ => some (.bool false)) (asserting (.readGlobal "missing")) =
    some (none, .delivering residual [assertionCaller] assertionFailure) := rfl

private def assertionNext : Closure.Executor.State :=
  .running residual.project assertionEnvironment.frame assertionTail [assertionCaller]

private def acceptsEquality (test : Closure.Executor.Operand calleeLayout) : Prop :=
  ∃ next, advanceIn table globals (asserting test) = some (none, next) ∧ next.project = assertionNext

example : acceptsEquality (.eqInt (.slot (.capture 0)) 7) :=
  stepIn_iff.mp (Closure.Executor.stepIn_iff.mpr rfl)

example : acceptsEquality (.eqInt (.global "argument") 11) :=
  stepIn_iff.mp (Closure.Executor.stepIn_iff.mpr rfl)

example : ∃ next, advanceIn table globals (asserting (.eqInt (.slot (.capture 0)) 11)) = some (none, next) ∧
    next.project = .delivering residual.project [assertionCaller] assertionFailure :=
  stepIn_iff.mp (Closure.Executor.stepIn_iff.mpr rfl)

private def missingEquality : State := asserting (.eqInt (.global "missing") 0)
private def missingResult : Result := .error (.nameError "missing")

private theorem missingEqualityRun :
    (semanticIn table.project globals).Execution missingEquality.project
      [none, some (.resume missingResult), none, some (.complete missingResult)]
      (.finished residual.project missingResult)
      [missingEquality.project, .delivering residual.project [assertionCaller] missingResult,
        .receiving residual.project assertionCaller [] missingResult,
        .delivering residual.project [] missingResult, .finished residual.project missingResult] :=
  .stepL (Closure.Executor.stepIn_iff.mpr rfl)
    (.stepL (.resume _ _ _ _) (.stepL (.receiveError _ _ _ _) (.stepL (.complete _ _) (.refl _))))

example : ∃ final states, (presentedIn table globals).Execution missingEquality
      [none, some (.resume missingResult), none, some (.complete missingResult)] final states ∧
    states.map State.project = [missingEquality.project, .delivering residual.project [assertionCaller] missingResult,
      .receiving residual.project assertionCaller [] missingResult,
      .delivering residual.project [] missingResult, .finished residual.project missingResult] ∧
    final.project = .finished residual.project missingResult :=
  executionIn_readback missingEqualityRun

private def unboundEquality : State :=
  .running { assertionEnvironment with heap } (.assert (.eqInt (.slot (.capture 0)) 0) assertionTail)
    [assertionCaller]

example : ∃ next, advanceIn table globals unboundEquality = some (none, next) ∧
    next.project = .delivering heap.project [assertionCaller] (.error (.unboundCapture 0)) :=
  stepIn_iff.mp (Closure.Executor.stepIn_iff.mpr rfl)

private def danglingEquality : State :=
  .running { assertionEnvironment with heap := HeapTable.empty }
    (.assert (.eqInt (.slot (.capture 0)) 0) assertionTail) [assertionCaller]

example : ∃ next, advanceIn table globals danglingEquality = some (some (.fault (.danglingCell ⟨0⟩)), next) ∧
    next.project = .faulted HeapTable.empty.project [assertionCaller] (.danglingCell ⟨0⟩) :=
  stepIn_iff.mp (Closure.Executor.stepIn_iff.mpr rfl)

private def compares (value : Value) (right : Int) : Except Failure Value :=
  let test : Closure.Executor.Operand calleeLayout := .eqInt (.global "value") right
  test.evalIn (fun _ => some value) residual.project assertionEnvironment.frame

example : compares (.int 7) 7 = .ok (.bool true) := rfl
example : compares (.int 7) 0 = .ok (.bool false) := rfl
example : compares (.bool false) 0 = .ok (.bool true) := rfl
example : compares (.bool true) 1 = .ok (.bool true) := rfl
example : compares (.bool true) 2 = .ok (.bool false) := rfl
example : compares .none 0 = .ok (.bool false) := rfl
example : compares (.function (frame.closure ref (fun _ => .owned 0))) 0 = .ok (.bool false) := rfl

end Silmaril.Languages.Python.Core.Closure.Finite.Executor
