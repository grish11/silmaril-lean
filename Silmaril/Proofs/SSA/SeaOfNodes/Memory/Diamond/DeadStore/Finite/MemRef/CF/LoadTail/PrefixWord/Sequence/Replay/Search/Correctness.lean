module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Search.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Search.Proofs

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.DeadStore (throughLoad)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations storeCount)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args}
variable {suffix : Memory.Graph (.word :: args)} {input : Tuple (Val cells) args} {entry : Memory.Graph args}

theorem find_checked {request : Request args preds} {stage : Emission cells args preds}
    (found : find fits arm suffix input entry = some (request, stage)) :
    request.version ∈ storeVersions entry ∧
      inferEntry request.version entry = some request.facts ∧
      inferCandidate preds request.facts.observed arm = some request.candidate ∧
      lowerWithEntry preds fits entry request.version arm request.candidate suffix input request.facts = some stage := by
  obtain ⟨version, member, attempted⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨facts, inferred, next⟩ := Option.bind_eq_some_iff.mp attempted
  obtain ⟨candidate, witnesses, next⟩ := Option.bind_eq_some_iff.mp next
  obtain ⟨emitted, accepted, packed⟩ := Option.bind_eq_some_iff.mp next
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj packed)
  exact ⟨member, inferred, witnesses, accepted⟩

private theorem run_replayed (fuel : Nat) (entry : Memory.Graph args) (current : Program cells args preds) :
    let result := run fits arm suffix input fuel entry current
    Replay.lowerFrom fits arm suffix input result.requests entry current = result.replay ∧
      result.replay.remaining = [] := by
  induction fuel generalizing entry current with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    simp only [run]
    split
    next empty => exact ⟨rfl, rfl⟩
    next request stage found =>
      obtain ⟨_, _, _, accepted⟩ := find_checked found
      obtain ⟨replayed, noPending⟩ := ih stage.edit.retained stage.programs.optimized
      refine ⟨?_, noPending⟩
      simp only [Replay.lowerFrom, accepted, replayed]

theorem lower_replayed :
    let result := lower preds fits entry arm suffix input
    Replay.lower preds fits entry arm suffix input result.requests = result.replay ∧
      result.replay.remaining = [] :=
  run_replayed (fits := fits) (arm := arm) (suffix := suffix) (input := input) (storeCount entry) entry
    (lowerBank preds fits cells (some entry) arm suffix)

private theorem run_exhausted (fuel : Nat) (entry : Memory.Graph args) (current : Program cells args preds)
    (enough : storeCount entry ≤ fuel) :
    find fits arm suffix input (run fits arm suffix input fuel entry current).replay.retained = none := by
  induction fuel generalizing entry current with
  | zero =>
    have versions : storeVersions entry = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough)
    simp [run, Replay.Result.stop, find, versions]
  | succ fuel ih =>
    rw [run]
    split
    next empty => exact empty
    next request stage found =>
      obtain ⟨_, _, _, accepted⟩ := find_checked found
      obtain ⟨cut, valid, _, _⟩ := lowerWithEntry_replay accepted
      have decrease := DeletesStores.storeCount_eq (cut_preserves cut valid).1
      exact ih stage.edit.retained stage.programs.optimized (by omega)

theorem lower_exhausted :
    let retained := (lower preds fits entry arm suffix input).replay.retained
    ∀ version ∈ storeVersions retained, tryVersion fits arm suffix input retained version = none := by
  apply List.findSome?_eq_none_iff.mp
  exact run_exhausted (storeCount entry) entry (lowerBank preds fits cells (some entry) arm suffix) (Nat.le_refl _)

theorem lower_observations (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower preds fits entry arm suffix input).replay.programs
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      CF.run programs.optimized programs.input arrival fuel initial =
        CF.run programs.original programs.input arrival fuel initial := by
  have observations := Replay.lower_observations (fits := fits) (entry := entry) (arm := arm) (suffix := suffix)
    (input := input) (requests := (lower preds fits entry arm suffix input).requests) arrival fuel initial
  rw [(lower_replayed (fits := fits) (entry := entry) (arm := arm) (suffix := suffix) (input := input)).1] at observations
  exact observations

theorem lower_retained (index : Nat) (initial : Buffer cells) :
    let result := (lower preds fits entry arm suffix input).replay
    let checkedInput := result.programs.input
    let probe := fun (graph : Memory.Graph args) => (throughLoad graph index).map fun block =>
      (observe block checkedInput initial).1
    DeletesStores result.deleted (operations entry) (operations result.retained) ∧
      (observe entry checkedInput initial).1 = (observe result.retained checkedInput initial).1 ∧
      probe entry = probe result.retained := by
  have retained := Replay.lower_retained (fits := fits) (entry := entry) (arm := arm) (suffix := suffix)
    (input := input) (requests := (lower preds fits entry arm suffix input).requests) index initial
  rw [(lower_replayed (fits := fits) (entry := entry) (arm := arm) (suffix := suffix) (input := input)).1] at retained
  exact retained

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Search.Proofs
