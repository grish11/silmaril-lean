module

public import Silmaril.Languages.Python.Core.Closure.Finite.Executor.Defs
import Silmaril.Languages.Python.Core.Closure.Executor.Thms
import Silmaril.Languages.Python.Core.Closure.Finite.Dispatch.Thms
import Silmaril.Languages.Python.Core.Closure.Finite.Thms
import Silmaril.Semantics.Operational.Projection.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Closure.Finite.Executor

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Finite
open Silmaril.Languages.Python.Core.Closure.Finite.Executor
open Silmaril.Languages.Python.Core.Closure.Executor (Continuation Event GlobalLookup Stack evalCallIn)
open Silmaril.Languages.Python.Core.Closure.Executor renaming advanceIn → coreAdvance,
  fail → coreFail, failDispatch → coreFailDispatch, resumeStore → coreResumeStore,
  enter → coreEnter, runPrefixIn → coreRunPrefix, stepIn_iff → coreStepIff,
  State → CoreState, Body → CoreBody
open Semantics.Operational

private theorem fail_project (heap : HeapTable) (stack : Stack) (error : Failure) :
    (fail heap stack error).project = coreFail heap.project stack error := by
  cases error <;> rfl

private theorem failDispatch_project (heap : HeapTable) (stack : Stack)
    (error : Silmaril.Languages.Python.Core.Closure.Dispatch.Failure) :
    (failDispatch heap stack error).project = coreFailDispatch heap.project stack error := by
  cases error with
  | call failure => exact fail_project heap stack failure
  | missingCode key => rfl
  | layoutMismatch expected actual => rfl

private theorem resumeStore_project {layout : Layout} (source : Snapshot layout) (destination : Slot layout)
    (value : Value) (body : CoreBody layout) (stack : Stack) :
    (resumeStore source destination value body stack).project =
      coreResumeStore source.heap.project source.frame destination value body stack := by
  unfold resumeStore coreResumeStore
  rw [← source.write_project destination value]
  cases source.write destination value with
  | error failure => exact fail_project source.heap stack failure
  | ok updated => rfl

private theorem enter_project (active : Silmaril.Languages.Python.Core.Closure.Finite.Dispatch.Active CoreBody Continuation) :
    (enter active).project = coreEnter active.project := rfl

theorem advanceIn_project (rows : CodeRows) (globals : GlobalLookup) (source : State) :
    (advanceIn rows globals source).map Transition.project = coreAdvance rows.project globals source.project := by
  cases source with
  | running environment body stack =>
    cases body with
    | ret operand =>
      simp only [advanceIn, coreAdvance, State.project, Option.map_some]
      cases operand.evalIn globals environment.heap.project environment.frame with
      | ok value => rfl
      | error failure => exact congrArg some (fail_project environment.heap stack failure)
    | store destination operand next =>
      simp only [advanceIn, coreAdvance, State.project, Option.map_some]
      cases operand.evalIn globals environment.heap.project environment.frame with
      | ok value => exact congrArg some (resumeStore_project environment destination value next stack)
      | error failure => exact congrArg some (fail_project environment.heap stack failure)
    | assert test next =>
      simp only [advanceIn, coreAdvance, State.project, Option.map_some]
      cases test.evalIn globals environment.heap.project environment.frame with
      | ok value => cases truth : value.truth <;> simp [truth, Transition.project, State.project]
      | error failure => exact congrArg some (fail_project environment.heap stack failure)
    | call destination callee arguments next =>
      simp only [advanceIn, coreAdvance, State.project, Option.map_some]
      cases evalCallIn globals environment.heap.project environment.frame callee arguments with
      | error failure => exact congrArg some (fail_project environment.heap stack failure)
      | ok inputs =>
        obtain ⟨value, values⟩ := inputs
        let caller : Call.Saved Continuation := ⟨_, environment.frame, ⟨destination, next⟩⟩
        have agrees := Dispatch.dispatch_project rows value values environment.heap caller stack
        simp only at *
        rw [← agrees]
        cases Dispatch.dispatch rows value values environment.heap caller stack with
        | ok active => exact congrArg (fun state => some (some (Event.enter value), state)) (enter_project active)
        | error failure => exact congrArg some (failDispatch_project environment.heap stack failure)
  | delivering heap stack result => cases stack <;> rfl
  | receiving heap caller stack result =>
    cases result with
    | ok value =>
      exact congrArg some (resumeStore_project ⟨heap, caller.frame⟩ caller.continuation.destination
        value caller.continuation.body stack)
    | error failure => rfl
  | finished heap result => rfl
  | faulted heap stack failure => rfl

theorem projectionIn (rows : CodeRows) (globals : GlobalLookup) :
    Projection (presentedIn rows globals) (semanticIn rows.project globals) State.project id where
  sound {source label target} step := by
    change advanceIn rows globals source = some (label, target) at step
    apply coreStepIff.mpr
    rw [← advanceIn_project rows globals source, step]
    rfl
  readback {source label target} step := by
    have agrees := coreStepIff.mp step
    rw [← advanceIn_project rows globals source] at agrees
    cases found : advanceIn rows globals source with
    | none =>
      rw [found] at agrees
      cases agrees
    | some pair =>
      obtain ⟨action, successor⟩ := pair
      rw [found] at agrees
      have eq : (action, successor.project) = (label, target) := Option.some.inj agrees
      exact ⟨action, successor, found, congrArg Prod.fst eq, congrArg Prod.snd eq⟩

theorem stepIn_iff {rows : CodeRows} {globals : GlobalLookup} {source : State} {label : Option Event} {target : CoreState} :
    (semanticIn rows.project globals).Tr source.project label target ↔
      ∃ successor, advanceIn rows globals source = some (label, successor) ∧ successor.project = target := by
  rw [(projectionIn rows globals).step_iff]
  constructor
  · rintro ⟨action, successor, moved, rfl, projected⟩
    exact ⟨successor, moved, projected⟩
  · rintro ⟨successor, moved, projected⟩
    exact ⟨label, successor, moved, rfl, projected⟩

theorem executionIn_readback {rows : CodeRows} {globals : GlobalLookup} {source : State} {labels : List (Option Event)}
    {target : CoreState} {states : List CoreState}
    (run : (semanticIn rows.project globals).Execution source.project labels target states) :
    ∃ final witnesses, (presentedIn rows globals).Execution source labels final witnesses ∧
      witnesses.map State.project = states ∧ final.project = target := by
  obtain ⟨final, labels', witnesses, lifted, labelsEq, statesEq, targetEq⟩ :=
    (projectionIn rows globals).execution_readback run rfl
  simp only [List.map_id] at labelsEq
  subst labels'
  exact ⟨final, witnesses, lifted, statesEq, targetEq⟩

theorem runPrefixIn_project (rows : CodeRows) (globals : GlobalLookup) (fuel : Nat) (source : State) :
    let next := runPrefixIn rows globals fuel source
    (next.1, next.2.project) = coreRunPrefix rows.project globals fuel source.project := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    simp only [runPrefixIn, coreRunPrefix]
    rw [← advanceIn_project rows globals source]
    cases found : advanceIn rows globals source with
    | none => rfl
    | some next =>
      obtain ⟨label, target⟩ := next
      have agrees := ih target
      change (_, _) = (label.toList ++ (coreRunPrefix rows.project globals fuel target.project).1,
        (coreRunPrefix rows.project globals fuel target.project).2)
      rw [← agrees]

end Silmaril.Proofs.Languages.Python.Core.Closure.Finite.Executor
