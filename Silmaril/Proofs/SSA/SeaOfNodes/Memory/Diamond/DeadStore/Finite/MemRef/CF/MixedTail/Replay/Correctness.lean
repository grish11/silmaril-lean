module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay.Proofs

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.DeadStore (throughLoad)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations storeCount)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args} {suffix : Memory.Graph (.word :: args)}
variable {input : Tuple (Val cells) args} {entry : Memory.Graph args}
variable {source : Program cells args preds} {requests : List Request} {result : Result cells args preds}

theorem check_accepted {request : Request} {stage : MixedTail.Result cells args preds}
    (checked : check fits arm suffix input entry request = some stage) :
    MixedTail.lower fits arm suffix input entry = some stage ∧ request.accepts stage.version = true := by
  obtain ⟨found, selected, packed⟩ := Option.bind_eq_some_iff.mp checked
  split at packed
  next version =>
    cases Option.some.inj packed
    exact ⟨selected, version⟩
  next => contradiction

private theorem lowerFrom_trace (exactSource : source = lowerBank preds fits cells (some entry) arm suffix) :
    Trace fits arm suffix input entry source requests (lowerFrom fits arm suffix input requests entry source) := by
  induction requests generalizing entry source with
  | nil => exact .done entry source
  | cons request rest ih =>
    rw [lowerFrom]
    split
    next refused => exact .refused source rest refused
    next stage checked =>
      obtain ⟨_, _, _, _, routes, programs⟩ := MixedTail.lower_checked (check_accepted checked).1
      exact .step checked ((congrArg Programs.original programs).trans exactSource.symm)
        (congrArg Programs.input programs) (fun i => by simpa [occurrenceRecords] using routes i)
        (ih (congrArg Programs.optimized programs))

theorem lower_trace :
    Trace fits arm suffix input entry (lowerBank preds fits cells (some entry) arm suffix) requests
      (lower preds fits entry arm suffix input requests) :=
  lowerFrom_trace rfl

private theorem trace_accounting (trace : Trace fits arm suffix input entry source requests result) :
    result.programs.input = input ∧ result.programs.original = source ∧
      result.remaining = requests.drop result.deleted := by
  induction trace with
  | done | refused => exact ⟨rfl, rfl, rfl⟩
  | step _ _ _ _ _ ih => exact ⟨rfl, rfl, ih.2.2⟩

theorem lower_accounting :
    let result := lower preds fits entry arm suffix input requests
    result.programs.input = input ∧ result.programs.original = lowerBank preds fits cells (some entry) arm suffix ∧
      result.remaining = requests.drop result.deleted :=
  trace_accounting lower_trace

private theorem trace_replayed (trace : Trace fits arm suffix input entry source requests result) :
    lowerFrom fits arm suffix input (result.admitted.map fun stage => .expect stage.version) entry source =
      { result with remaining := [] } := by
  induction trace with
  | done | refused => rfl
  | @step entry source _ _ stage _ checked _ _ _ _ ih =>
    have accepted := (check_accepted checked).1
    have expected : check fits arm suffix input entry (.expect stage.version) = some stage := by
      simp [check, accepted, Request.accepts]
    change lowerFrom fits arm suffix input (.expect stage.version :: _) entry source = _
    rw [lowerFrom, expected]
    dsimp only
    rw [ih]
    rfl

theorem lower_replayed :
    let result := lower preds fits entry arm suffix input requests
    lower preds fits entry arm suffix input (result.admitted.map fun stage => .expect stage.version) =
      { result with remaining := [] } :=
  trace_replayed lower_trace

private theorem run_exhausted (fuel : Nat) (entry : Memory.Graph args) (current : Program cells args preds)
    (enough : storeCount entry ≤ fuel) :
    MixedTail.lower fits arm suffix input
      (lowerFrom fits arm suffix input (List.replicate fuel .discover) entry current).retained = none := by
  induction fuel generalizing entry current with
  | zero =>
    have versions : storeVersions entry = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough)
    apply MixedTail.lower_eq_none_iff.mpr
    intro version member
    change version ∈ storeVersions entry at member
    simp [versions] at member
  | succ fuel ih =>
    simp only [List.replicate_succ, lowerFrom]
    split
    next refused =>
      cases found : MixedTail.lower fits arm suffix input entry with
      | none => exact found
      | some stage => simp [check, found, Request.accepts] at refused
    next stage checked =>
      obtain ⟨_, inferred, valid, _, _, _⟩ := MixedTail.lower_checked (check_accepted checked).1
      have decrease := DeletesStores.storeCount_eq (MixedTail.inferCut_observations inferred valid).1
      exact ih stage.emission.edit.retained stage.emission.programs.optimized (by omega)

theorem discover_exhausted :
    let retained := (discover preds fits entry arm suffix input).retained
    ∀ version ∈ storeVersions retained, tryVersion fits arm suffix input retained version = none :=
  MixedTail.lower_eq_none_iff.mp
    (run_exhausted (storeCount entry) entry (lowerBank preds fits cells (some entry) arm suffix) (Nat.le_refl _))

private theorem trace_observations (trace : Trace fits arm suffix input entry source requests result)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let before := entryTransition source input arrival initial
    let after := entryTransition result.programs.optimized input arrival initial
    after.1 = before.1 ∧
      armTransition result.programs.optimized input arrival after.2 = armTransition source input arrival before.2 ∧
      run result.programs.optimized input arrival fuel initial = run source input arrival fuel initial := by
  induction trace with
  | done | refused => exact ⟨rfl, rfl, rfl⟩
  | step checked sourceEq inputEq _ _ ih =>
    have step := MixedTail.lower_observations (check_accepted checked).1 arrival fuel initial
    dsimp only at step
    rw [sourceEq, inputEq] at step
    obtain ⟨firstSlot, nextSlot, joined, returned⟩ := step
    exact ⟨ih.1.trans (nextSlot.trans firstSlot.symm), ih.2.1.trans joined, ih.2.2.trans returned⟩

theorem lower_observations (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower preds fits entry arm suffix input requests).programs
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.optimized programs.input arrival fuel initial = run programs.original programs.input arrival fuel initial := by
  have trace := lower_trace (fits := fits) (arm := arm) (suffix := suffix) (input := input)
    (entry := entry) (requests := requests)
  obtain ⟨checkedInput, original, _⟩ := trace_accounting trace
  obtain ⟨slot, joined, returned⟩ := trace_observations trace arrival fuel initial
  have selected := congrArg Prod.fst (lowerBank_entry fits (some entry) arm suffix input arrival initial)
  dsimp only
  rw [checkedInput, original]
  exact ⟨selected, slot.trans selected, joined, returned⟩

private theorem trace_entry (trace : Trace fits arm suffix input entry source requests result)
    (initial : Buffer cells) :
    let probe := fun (graph : Memory.Graph args) (index : Nat) => (throughLoad graph index).map fun block =>
      (observe block input initial).1
    DeletesStores result.deleted (operations entry) (operations result.retained) ∧
      observe entry input initial = ((observe result.retained input initial).1, result.restoreEntry initial) ∧
      ∀ index, probe entry index = probe result.retained index := by
  induction trace with
  | done | refused => exact ⟨DeletesStores.refl _, rfl, fun _ => rfl⟩
  | step checked _ inputEq _ next ih =>
    obtain ⟨order, value, reads⟩ := MixedTail.lower_entry (check_accepted checked).1 initial
    rw [inputEq] at value reads
    obtain ⟨nextOrder, nextValue, nextReads⟩ := ih
    refine ⟨?_, ?_, fun index => (reads index).trans (nextReads index)⟩
    · simpa only [Result.deleted, Result.prepend, List.length_cons, Nat.one_add] using order.trans nextOrder
    · rw [value, nextValue]
      simp only [Result.restoreEntry, Result.prepend, List.foldr_cons, (trace_accounting next).1]

theorem lower_entry (initial : Buffer cells) :
    let result := lower preds fits entry arm suffix input requests
    let checkedInput := result.programs.input
    let probe := fun (graph : Memory.Graph args) (index : Nat) => (throughLoad graph index).map fun block =>
      (observe block checkedInput initial).1
    DeletesStores result.deleted (operations entry) (operations result.retained) ∧
      observe entry checkedInput initial = ((observe result.retained checkedInput initial).1, result.restoreEntry initial) ∧
      ∀ index, probe entry index = probe result.retained index := by
  have trace := lower_trace (fits := fits) (arm := arm) (suffix := suffix) (input := input)
    (entry := entry) (requests := requests)
  simpa only [(trace_accounting trace).1] using trace_entry trace initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay.Proofs
