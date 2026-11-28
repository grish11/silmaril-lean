module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Proofs

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.DeadStore (throughLoad)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe lower_run)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args} {suffix : Memory.Graph (.word :: args)}
variable {input : Tuple (Val cells) args} {entry : Memory.Graph args}
variable {source : Program cells args preds} {requests : List (Request args preds)}
variable {result : Result cells args preds}

private theorem lowerFrom_trace (exactSource : source = lowerBank preds fits cells (some entry) arm suffix) :
    Trace fits arm suffix input entry source requests (lowerFrom fits arm suffix input requests entry source) := by
  induction requests generalizing entry source with
  | nil => exact .done entry source
  | cons request rest ih =>
    rw [lowerFrom]
    split
    next checked => exact .refused source rest checked
    next stage checked =>
      have programs := (lowerWithEntry_replay checked).2.2.2
      exact .step checked ((congrArg Programs.original programs).trans exactSource.symm)
        (congrArg Programs.input programs) (ih (congrArg Programs.optimized programs))

theorem lower_trace :
    Trace fits arm suffix input entry (lowerBank preds fits cells (some entry) arm suffix) requests
      (lower preds fits entry arm suffix input requests) :=
  lowerFrom_trace rfl

private theorem trace_accounting (trace : Trace fits arm suffix input entry source requests result) :
    result.programs.input = input ∧ result.programs.original = source ∧
      result.remaining = requests.drop result.deleted := by
  induction trace with
  | done | refused => exact ⟨rfl, rfl, rfl⟩
  | step _ _ _ _ ih => exact ⟨rfl, rfl, ih.2.2⟩

theorem lower_accounting :
    let result := lower preds fits entry arm suffix input requests
    result.programs.input = input ∧ result.programs.original = lowerBank preds fits cells (some entry) arm suffix ∧
      result.remaining = requests.drop result.deleted :=
  trace_accounting lower_trace

private theorem trace_observations (trace : Trace fits arm suffix input entry source requests result)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let before := entryTransition source input arrival initial
    let after := entryTransition result.programs.optimized input arrival initial
    after.1 = before.1 ∧
      armTransition result.programs.optimized input arrival after.2 = armTransition source input arrival before.2 ∧
      run result.programs.optimized input arrival fuel initial = run source input arrival fuel initial := by
  induction trace with
  | done | refused => exact ⟨rfl, rfl, rfl⟩
  | step checked sourceEq inputEq _ ih =>
    have observations := PrefixWord.lower_observations (lowerWithEntry_programs checked) arrival fuel initial
    rw [sourceEq, inputEq] at observations
    obtain ⟨firstSlot, nextSlot, nextJoin, firstRun, nextRun⟩ := observations
    exact ⟨ih.1.trans (nextSlot.trans firstSlot.symm), ih.2.1.trans nextJoin,
      ih.2.2.trans (nextRun.trans firstRun.symm)⟩

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

private theorem trace_retained (trace : Trace fits arm suffix input entry source requests result)
    (index : Nat) (initial : Buffer cells) :
    let probe := fun (graph : Memory.Graph args) => (throughLoad graph index).map fun block =>
      (observe block input initial).1
    DeletesStores result.deleted (operations entry) (operations result.retained) ∧
      (observe entry input initial).1 = (observe result.retained input initial).1 ∧
      probe entry = probe result.retained := by
  induction trace with
  | done | refused => exact ⟨DeletesStores.refl _, rfl, rfl⟩
  | step checked _ inputEq _ ih =>
    obtain ⟨cut, valid, _, _⟩ := lowerWithEntry_replay checked
    obtain ⟨order, transfer⟩ := cut_preserves cut valid
    have words := congrArg Prod.fst (transfer PUnit.unit initial.cell).2
    have reads := lower_readbacks (lowerWithEntry_programs checked) cut index initial
    rw [inputEq] at reads
    have words := show (observe _ input initial).1 = (observe _ input initial).1 by
      simpa only [lower_run, Memory.Graph.denote] using words
    exact ⟨by simpa only [Result.deleted, Result.prepend, List.length_cons, Nat.one_add] using order.trans ih.1,
      words.trans ih.2.1, reads.trans ih.2.2⟩

theorem lower_retained (index : Nat) (initial : Buffer cells) :
    let result := lower preds fits entry arm suffix input requests
    let checkedInput := result.programs.input
    let probe := fun (graph : Memory.Graph args) => (throughLoad graph index).map fun block =>
      (observe block checkedInput initial).1
    DeletesStores result.deleted (operations entry) (operations result.retained) ∧
      (observe entry checkedInput initial).1 = (observe result.retained checkedInput initial).1 ∧
      probe entry = probe result.retained := by
  have trace := lower_trace (fits := fits) (arm := arm) (suffix := suffix) (input := input)
    (entry := entry) (requests := requests)
  simpa only [(trace_accounting trace).1] using trace_retained trace index initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Proofs
