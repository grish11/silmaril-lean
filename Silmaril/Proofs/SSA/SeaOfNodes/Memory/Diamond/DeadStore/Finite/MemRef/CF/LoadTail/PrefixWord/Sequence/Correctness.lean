module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Proofs

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.DeadStore (throughLoad)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe lower_run)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {entry : Memory.Graph args} {input : Tuple (Val cells) args}
variable {arm : Occurrence preds → Memory.Graph args} {suffix : Memory.Graph (.word :: args)}
variable {first second : Request args preds} {result : Result cells args preds}

theorem lower_replay (emitted : lower preds fits entry arm suffix input first second = some result) :
    lowerWithEntry preds fits entry first.version arm first.candidate suffix input first.facts = some result.first ∧
    lowerWithEntry preds fits result.first.edit.retained second.version arm second.candidate suffix input second.facts =
      result.second ∧
    match result.second with
    | none => True
    | some next =>
      next.programs.original = result.first.programs.optimized ∧ next.programs.input = result.first.programs.input := by
  obtain ⟨stage, accepted, packed⟩ := Option.bind_eq_some_iff.mp emitted
  cases Option.some.inj packed
  refine ⟨accepted, rfl, ?_⟩
  dsimp only
  cases checked : lowerWithEntry preds fits stage.edit.retained second.version arm second.candidate suffix input
      second.facts with
  | none => exact True.intro
  | some next =>
    have stagePrograms := (lowerWithEntry_replay accepted).2.2.2
    have nextPrograms := (lowerWithEntry_replay checked).2.2.2
    change next.programs.original = stage.programs.optimized ∧ next.programs.input = stage.programs.input
    rw [stagePrograms, nextPrograms]
    exact ⟨rfl, rfl⟩

theorem lower_observations (emitted : lower preds fits entry arm suffix input first second = some result)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := result.programs
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.optimized programs.input arrival fuel initial = run programs.original programs.input arrival fuel initial := by
  obtain ⟨accepted, checked, link⟩ := lower_replay emitted
  obtain ⟨before, middle, firstJoin, originalReturns, middleReturns⟩ :=
    PrefixWord.lower_observations (lowerWithEntry_programs accepted) arrival fuel initial
  have firstRun := middleReturns.trans originalReturns.symm
  cases outcome : result.second with
  | none =>
    simpa only [Result.programs, outcome] using And.intro before ⟨middle, firstJoin, firstRun⟩
  | some next =>
    rw [outcome] at checked link
    have observations := PrefixWord.lower_observations (lowerWithEntry_programs checked) arrival fuel initial
    rw [link.1, link.2] at observations
    obtain ⟨_, after, nextJoin, middleReturns, finalReturns⟩ := observations
    simp only [Result.programs, outcome]
    exact ⟨before, after, nextJoin.trans firstJoin, (finalReturns.trans middleReturns.symm).trans firstRun⟩

private theorem step_retained {request : Request args preds} {emission : Emission cells args preds}
    (accepted : lowerWithEntry preds fits entry request.version arm request.candidate suffix input request.facts =
      some emission) (index : Nat) (initial : Buffer cells) :
    DeletesStores 1 (operations entry) (operations emission.edit.retained) ∧
    (observe entry input initial).1 = (observe emission.edit.retained input initial).1 ∧
    ((throughLoad entry index).map fun block => (observe block input initial).1) =
      ((throughLoad emission.edit.retained index).map fun block => (observe block input initial).1) := by
  obtain ⟨cut, valid, _, programs⟩ := lowerWithEntry_replay accepted
  obtain ⟨order, transfer⟩ := cut_preserves cut valid
  have words := congrArg Prod.fst (transfer PUnit.unit initial.cell).2
  have reads := lower_readbacks (lowerWithEntry_programs accepted) cut index initial
  rw [programs] at reads
  exact ⟨order, by simpa only [lower_run, Memory.Graph.denote] using words, reads⟩

theorem lower_retained (emitted : lower preds fits entry arm suffix input first second = some result)
    (index : Nat) (initial : Buffer cells) :
    let checkedInput := result.programs.input
    let probe := fun (graph : Memory.Graph args) => (throughLoad graph index).map fun block =>
      (observe block checkedInput initial).1
    DeletesStores result.deleted (operations entry) (operations result.retained) ∧
      (observe entry checkedInput initial).1 = (observe result.retained checkedInput initial).1 ∧
      probe entry = probe result.retained := by
  obtain ⟨accepted, checked, _⟩ := lower_replay emitted
  have programs := (lowerWithEntry_replay accepted).2.2.2
  have checkedInput : result.first.programs.input = input := congrArg Programs.input programs
  obtain ⟨order, word, reads⟩ := step_retained accepted index initial
  cases outcome : result.second with
  | none =>
    simp only [Result.programs, Result.deleted, Result.retained, outcome, checkedInput]
    exact ⟨order, word, reads⟩
  | some next =>
    rw [outcome] at checked
    obtain ⟨nextOrder, nextWord, nextReads⟩ := step_retained checked index initial
    simp only [Result.programs, Result.deleted, Result.retained, outcome, Option.isSome_some,
      Option.getD_some, ite_true, checkedInput]
    exact ⟨order.trans nextOrder, word.trans nextWord, reads.trans nextReads⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Proofs
