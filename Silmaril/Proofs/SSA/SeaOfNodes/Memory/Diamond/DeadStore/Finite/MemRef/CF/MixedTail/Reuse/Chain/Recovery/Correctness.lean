module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Recovery.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Recovery.Proofs

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
variable {current : Program cells args preds} {stages : List (MixedTail.Result cells args preds)}
variable {checked : Chain.Result cells args preds}

private theorem trace_emitted (traced : Chain.Trace fits arm suffix input entry current stages checked)
    (emitted : current = lowerBank preds fits cells (some entry) arm suffix) :
    checked.replay.programs.optimized = lowerBank preds fits cells (some checked.replay.retained) arm suffix := by
  induction traced with
  | done | refused => exact emitted
  | step _ selected _ _ _ ih =>
    obtain ⟨_, _, _, _, _, programs⟩ := MixedTail.tryVersion_checked selected
    exact ih (congrArg Programs.optimized programs)

private theorem prefix_emitted
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) :
    let accepted := (Chain.lower original entry input).replay
    accepted.programs.optimized = lowerBank preds fits cells (some accepted.retained) arm suffix := by
  have source : original.programs.original = lowerBank preds fits cells (some entry) arm suffix := by
    cases recorded <;> rfl
  exact trace_emitted (Chain.lower_trace recorded) source

theorem lower_diagnostic :
    (lower original entry fits arm suffix input).diagnostic = Diagnostic.lower original entry input := rfl

theorem lower_fresh
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) :
    let diagnostic := Diagnostic.lower original entry input
    (lower original entry fits arm suffix input).fresh = diagnostic.refusal.map fun _ =>
      Replay.discover preds fits diagnostic.checkedPrefix.replay.retained arm suffix input := by
  have saved := (Chain.lower_accounting (input := input) recorded).1
  have emitted := prefix_emitted (input := input) recorded
  simp only [lower, Diagnostic.lower_prefix, saved, emitted, Replay.discover, Replay.lower, requestsFor]

theorem lower_fresh_trace
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) {fresh : Replay.Result cells args preds}
    (resumed : (lower original entry fits arm suffix input).fresh = some fresh) :
    let accepted := (lower original entry fits arm suffix input).diagnostic.checkedPrefix.replay
    fresh.programs.original = accepted.programs.optimized ∧ fresh.programs.input = input ∧
      Replay.Trace fits arm suffix input accepted.retained accepted.programs.optimized (requestsFor accepted.retained) fresh := by
  rw [lower_fresh recorded] at resumed
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp resumed
  let accepted := (Chain.lower original entry input).replay
  have ⟨saved, source, _⟩ := Replay.lower_accounting (fits := fits) (arm := arm) (suffix := suffix)
    (input := input) (entry := accepted.retained) (requests := requestsFor accepted.retained)
  simp only [lower_diagnostic, Diagnostic.lower_prefix, prefix_emitted (input := input) recorded, Replay.discover]
  exact ⟨source, saved, Replay.lower_trace⟩

private theorem trace_no_edits {fresh : Replay.Result cells args preds}
    (traced : Replay.Trace fits arm suffix input entry current requests fresh)
    (empty : fresh.admitted = []) : fresh.programs.optimized = current ∧ fresh.retained = entry := by
  cases traced with
  | done | refused => exact ⟨rfl, rfl⟩
  | step => cases empty

theorem lower_no_fresh_cuts
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original)
    (zero : ((lower original entry fits arm suffix input).fresh.map Replay.Result.deleted).getD 0 = 0) :
    let result := lower original entry fits arm suffix input
    let accepted := result.diagnostic.checkedPrefix.replay
    result.optimized = accepted.programs.optimized ∧ result.retained = accepted.retained := by
  cases resumed : (lower original entry fits arm suffix input).fresh with
  | none => simp only [Result.optimized, Result.retained, resumed, Option.map_none, Option.getD_none, and_self]
  | some fresh =>
    have empty : fresh.admitted = [] := by
      simpa [resumed, Replay.Result.deleted] using zero
    have traced := (lower_fresh_trace recorded resumed).2.2
    have endpoints := trace_no_edits traced empty
    simpa only [Result.optimized, Result.retained, resumed, Option.map_some, Option.getD_some] using endpoints

theorem lower_observations
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let result := lower original entry fits arm suffix input
    let before := entryTransition original.programs.original input arrival initial
    let after := entryTransition result.optimized input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition result.optimized input arrival after.2 =
        armTransition original.programs.original input arrival before.2 ∧
      run result.optimized input arrival fuel initial = run original.programs.original input arrival fuel initial := by
  let accepted := (Chain.lower original entry input).replay
  obtain ⟨saved, source, _, _⟩ := Chain.lower_accounting (input := input) recorded
  have preserved := Chain.lower_observations (input := input) recorded arrival fuel initial
  dsimp only at preserved
  rw [saved, source] at preserved
  cases refusal : (Diagnostic.lower original entry input).refusal with
  | none =>
    simpa only [Result.optimized, lower_fresh recorded, refusal, Option.map_none, Option.getD_none,
      lower_diagnostic, Diagnostic.lower_prefix] using preserved
  | some report =>
    have endpoint : (lower original entry fits arm suffix input).optimized =
        (Replay.discover preds fits accepted.retained arm suffix input).programs.optimized := by
      simp only [Result.optimized, lower_fresh recorded, refusal, Option.map_some, Option.getD_some,
        Diagnostic.lower_prefix, accepted]
    have recovered := Replay.lower_observations (fits := fits) (arm := arm) (suffix := suffix)
      (input := input) (entry := accepted.retained) (requests := requestsFor accepted.retained) arrival fuel initial
    have ⟨freshInput, freshSource, _⟩ := Replay.lower_accounting (fits := fits) (arm := arm) (suffix := suffix)
      (input := input) (entry := accepted.retained) (requests := requestsFor accepted.retained)
    dsimp only at freshInput freshSource recovered
    rw [freshInput, freshSource, ← prefix_emitted (input := input) recorded] at recovered
    obtain ⟨_, selected, joined, returned⟩ := recovered
    obtain ⟨before, _, acceptedJoin, acceptedReturn⟩ := preserved
    dsimp only
    rw [endpoint]
    exact ⟨before, selected, joined.trans acceptedJoin, returned.trans acceptedReturn⟩

theorem lower_entry
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) (initial : Buffer cells) :
    let result := lower original entry fits arm suffix input
    let probe := fun (graph : Memory.Graph args) (index : Nat) => (throughLoad graph index).map fun block =>
      (observe block input initial).1
    DeletesStores result.deleted (operations entry) (operations result.retained) ∧
      (observe result.retained input initial).1 = (observe entry input initial).1 ∧
      ∀ index, probe entry index = probe result.retained index := by
  let accepted := (Chain.lower original entry input).replay
  have saved := (Chain.lower_accounting (input := input) recorded).1
  have preserved := Chain.lower_entry (input := input) recorded initial
  dsimp only at preserved
  rw [saved] at preserved
  obtain ⟨ordered, restored, reads⟩ := preserved
  have word := congrArg Prod.fst restored
  cases refusal : (Diagnostic.lower original entry input).refusal with
  | none =>
    simpa only [Result.retained, Result.deleted, lower_fresh recorded, refusal, Option.map_none,
      Option.getD_none, Nat.add_zero, lower_diagnostic, Diagnostic.lower_prefix] using And.intro ordered (And.intro word.symm reads)
  | some report =>
    have recovered := Replay.lower_entry (fits := fits) (arm := arm) (suffix := suffix)
      (input := input) (entry := accepted.retained) (requests := requestsFor accepted.retained) initial
    have freshInput := (Replay.lower_accounting (fits := fits) (arm := arm) (suffix := suffix)
      (input := input) (entry := accepted.retained) (requests := requestsFor accepted.retained)).1
    dsimp only at recovered
    rw [freshInput] at recovered
    obtain ⟨freshOrder, freshRestore, freshReads⟩ := recovered
    simp only [Result.retained, Result.deleted, lower_fresh recorded, refusal, Option.map_some,
      Option.getD_some, lower_diagnostic, Diagnostic.lower_prefix]
    exact ⟨ordered.trans freshOrder, (congrArg Prod.fst freshRestore).symm.trans word.symm,
      fun index => (reads index).trans (freshReads index)⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Recovery.Proofs
