module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Proofs

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.DeadStore (throughLoad)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open SeaOfNodes.Memory.MLIR.MemRef (observe)
open Silmaril.MLIR.MemRef (Buffer)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args} {suffix : Memory.Graph (.word :: args)}
variable {input oldInput : Tuple (Val cells) args} {entry : Memory.Graph args}
variable {requests : List Replay.Request} {original : Replay.Result cells args preds}
variable {source : Program cells args preds} {stages : List (MixedTail.Result cells args preds)}
variable {result : Result cells args preds}

theorem check_iff_valid : check original input = true ↔ Valid original input := by
  simp only [check, Valid, List.all_eq_true, Contract.check_iff_valid]

private theorem recorded_source (recorded : Replay.Trace fits arm suffix oldInput entry source requests original) :
    original.programs.original = source := by
  cases recorded <;> rfl

private theorem from_trace (recorded : Replay.Trace fits arm suffix oldInput entry source requests original) :
    Trace fits arm suffix input entry source original.admitted (lowerFrom input original.admitted entry source) := by
  induction recorded with
  | done entry source | refused source _ _ => exact .done _ source
  | @step entry source _ _ stage _ accepted sourceEq _ _ _ ih =>
    change Trace fits arm suffix input entry source (stage :: _) (lowerFrom input (stage :: _) entry source)
    rw [lowerFrom]
    split
    next rejected => exact .refused source _ rejected
    next rebound checked =>
      obtain ⟨selected, saved, originalEq, _⟩ := reuse_checked (Replay.check_accepted accepted).1 checked
      obtain ⟨_, rfl⟩ := reuse_eq_some_iff.mp checked
      exact .step checked selected (originalEq.trans sourceEq) saved ih

theorem lower_trace
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) :
    Trace fits arm suffix input entry original.programs.original original.admitted (lower original entry input) := by
  unfold lower
  rw [recorded_source recorded]
  exact from_trace recorded

private theorem trace_accounting (traced : Trace fits arm suffix input entry source stages result) :
    result.replay.programs.input = input ∧ result.replay.programs.original = source ∧
      result.replay.admitted = (stages.take result.replay.deleted).map (fun stage => atInput stage input) ∧
      result.pending = stages.drop result.replay.deleted := by
  induction traced with
  | done | refused => exact ⟨rfl, rfl, rfl, rfl⟩
  | step checked _ _ _ _ ih =>
    obtain ⟨_, rfl⟩ := reuse_eq_some_iff.mp checked
    exact ⟨rfl, rfl, congrArg (List.cons _) ih.2.2.1, ih.2.2.2⟩

theorem lower_accounting
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) :
    let result := lower original entry input
    result.replay.programs.input = input ∧ result.replay.programs.original = original.programs.original ∧
      result.replay.admitted =
        (original.admitted.take result.replay.deleted).map (fun stage => atInput stage input) ∧
      result.pending = original.admitted.drop result.replay.deleted :=
  trace_accounting (lower_trace recorded)

private theorem trace_complete (traced : Trace fits arm suffix input entry source stages result) :
    result.pending = [] ↔ ∀ stage ∈ stages, (contractOf stage).Valid input := by
  induction traced with
  | done => simp [Result.stop]
  | refused _ _ rejected =>
    have invalid := reuse_eq_none_iff.mp rejected
    simp [Result.stop, invalid]
  | step checked _ _ _ _ ih =>
    have valid := (reuse_eq_some_iff.mp checked).1
    simpa [Result.prepend, List.forall_mem_cons, valid] using ih

theorem lower_complete
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) :
    (lower original entry input).pending = [] ↔ Valid original input := by
  rw [trace_complete (lower_trace recorded)]
  constructor
  · intro valid facts member
    obtain ⟨stage, present, rfl⟩ := List.mem_map.mp member
    exact valid stage present
  · intro valid stage present
    exact valid _ (List.mem_map.mpr ⟨stage, present, rfl⟩)

private theorem trace_endpoint (traced : Trace fits arm suffix input entry source stages result) :
    (result.replay.programs.optimized, result.replay.retained) =
      (result.replay.admitted.getLast?.map fun stage =>
        (stage.emission.programs.optimized, stage.emission.edit.retained)).getD (source, entry) := by
  induction traced with
  | done | refused => rfl
  | @step _ _ _ rebound _ tail _ _ _ _ _ ih =>
    cases ending : tail.replay.admitted.getLast? with
    | none => simpa [Result.prepend, Replay.Result.prepend, List.getLast?_cons, ending] using ih
    | some last => simpa [Result.prepend, Replay.Result.prepend, List.getLast?_cons, ending] using ih

theorem lower_endpoint
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) :
    let result := lower original entry input
    (result.replay.programs.optimized, result.replay.retained) =
      (result.replay.admitted.getLast?.map fun stage =>
        (stage.emission.programs.optimized, stage.emission.edit.retained)).getD (original.programs.original, entry) :=
  trace_endpoint (lower_trace recorded)

private theorem from_complete (recorded : Replay.Trace fits arm suffix oldInput entry source requests original) :
    let result := lowerFrom input original.admitted entry source
    result.pending = [] →
      result.replay.programs.optimized = original.programs.optimized ∧ result.replay.retained = original.retained := by
  induction recorded with
  | done | refused => exact fun _ => ⟨rfl, rfl⟩
  | step _ _ _ _ _ ih =>
    simp only [Replay.Result.prepend, lowerFrom]
    split
    next => simp [Result.stop]
    next rebound checked =>
      obtain ⟨_, rfl⟩ := reuse_eq_some_iff.mp checked
      exact ih

theorem lower_complete_artifacts
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) (complete : (lower original entry input).pending = []) :
    let result := (lower original entry input).replay
    result.programs.optimized = original.programs.optimized ∧ result.retained = original.retained := by
  unfold lower at complete ⊢
  rw [recorded_source recorded] at complete ⊢
  exact from_complete recorded complete

private theorem trace_observations (traced : Trace fits arm suffix input entry source stages result)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let before := entryTransition source input arrival initial
    let after := entryTransition result.replay.programs.optimized input arrival initial
    after.1 = before.1 ∧
      armTransition result.replay.programs.optimized input arrival after.2 =
        armTransition source input arrival before.2 ∧
      run result.replay.programs.optimized input arrival fuel initial = run source input arrival fuel initial := by
  induction traced with
  | done | refused => exact ⟨rfl, rfl, rfl⟩
  | step _ selected sourceEq inputEq _ ih =>
    have step := MixedTail.tryVersion_observations selected arrival fuel initial
    dsimp only at step
    rw [sourceEq, inputEq] at step
    obtain ⟨firstSlot, nextSlot, joined, returned⟩ := step
    exact ⟨ih.1.trans (nextSlot.trans firstSlot.symm), ih.2.1.trans joined, ih.2.2.trans returned⟩

theorem lower_observations
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower original entry input).replay.programs
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.optimized programs.input arrival fuel initial = run programs.original programs.input arrival fuel initial := by
  have traced := lower_trace (input := input) recorded
  obtain ⟨saved, source, _, _⟩ := trace_accounting traced
  obtain ⟨slot, joined, returned⟩ := trace_observations traced arrival fuel initial
  have selected := congrArg Prod.fst (lowerBank_entry fits (some entry) arm suffix input arrival initial)
  have before := (congrArg (fun program => (entryTransition program input arrival initial).1) (recorded_source recorded)).trans selected
  dsimp only
  rw [saved, source]
  exact ⟨before, slot.trans before, joined, returned⟩

private theorem trace_entry (traced : Trace fits arm suffix input entry source stages result)
    (initial : Buffer cells) :
    let replay := result.replay
    let probe := fun (graph : Memory.Graph args) (index : Nat) => (throughLoad graph index).map fun block =>
      (observe block input initial).1
    DeletesStores replay.deleted (operations entry) (operations replay.retained) ∧
      observe entry input initial = ((observe replay.retained input initial).1, replay.restoreEntry initial) ∧
      ∀ index, probe entry index = probe replay.retained index := by
  induction traced with
  | done | refused => exact ⟨DeletesStores.refl _, rfl, fun _ => rfl⟩
  | step _ selected _ inputEq next ih =>
    obtain ⟨order, value, reads⟩ := MixedTail.tryVersion_entry selected initial
    rw [inputEq] at value reads
    obtain ⟨nextOrder, nextValue, nextReads⟩ := ih
    refine ⟨?_, ?_, fun index => (reads index).trans (nextReads index)⟩
    · simpa only [Result.prepend, Replay.Result.deleted, Replay.Result.prepend, List.length_cons, Nat.one_add]
        using order.trans nextOrder
    · rw [value, nextValue]
      simp only [Result.prepend, Replay.Result.restoreEntry, Replay.Result.prepend, List.foldr_cons, (trace_accounting next).1]

theorem lower_entry
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) (initial : Buffer cells) :
    let replay := (lower original entry input).replay
    let checkedInput := replay.programs.input
    let probe := fun (graph : Memory.Graph args) (index : Nat) => (throughLoad graph index).map fun block =>
      (observe block checkedInput initial).1
    DeletesStores replay.deleted (operations entry) (operations replay.retained) ∧
      observe entry checkedInput initial = ((observe replay.retained checkedInput initial).1, replay.restoreEntry initial) ∧
      ∀ index, probe entry index = probe replay.retained index := by
  have traced := lower_trace (input := input) recorded
  simpa only [(trace_accounting traced).1] using trace_entry traced initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Proofs
