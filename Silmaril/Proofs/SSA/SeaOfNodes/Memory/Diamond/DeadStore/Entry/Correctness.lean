module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Defs
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Proofs

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.DeadStore.Search.Selection.Readers renaming discover → discoverReaders
open Discovery.MemRef.CF (Programs entryTransition lowerDiamond lowerDiamond_entryTransition lowerDiamond_run run)

variable {args : List ValueSort} {cells : Nat}
variable {entry edited : Memory.Graph args}

theorem rewrite_checked (input : Tuple (Val cells) args) (accepted : rewrite entry input = some edited) :
    (storeVersions entry).length = 2 ∧
      ∃ facts, discoverReaders entry 1 = some facts ∧
        Memory.DeadStore.rewrite entry ⟨1, 2⟩ facts input = some edited := by
  unfold rewrite at accepted
  split at accepted
  next count =>
    obtain ⟨facts, found, checked⟩ := Option.bind_eq_some_iff.mp accepted
    exact ⟨count, facts, found, checked⟩
  next => cases accepted

theorem rewrite_denote (input : Tuple (Val cells) args) (accepted : rewrite entry input = some edited)
    (initial : Heap cells) : edited.denote input initial = entry.denote input initial := by
  obtain ⟨_, _, _, checked⟩ := rewrite_checked input accepted
  obtain ⟨structural, valid⟩ := (Memory.DeadStore.rewrite_eq_some_iff input).mp checked
  exact Memory.DeadStore.rewriteWith_denote structural input valid initial

theorem lower_entryTransition_eq {graph : Graph args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (emitted : lower graph entry input = some programs)
    (guard : Bool) (initial : Buffer cells) :
    entryTransition programs.optimized programs.input guard initial =
      entryTransition programs.original programs.input guard initial := by
  obtain ⟨edited, accepted, rfl⟩ := Option.map_eq_some_iff.mp emitted
  change entryTransition (lowerDiamond cells graph (some edited)) input guard initial =
    entryTransition (lowerDiamond cells graph (some entry)) input guard initial
  rw [lowerDiamond_entryTransition, lowerDiamond_entryTransition]
  simp only [rewrite_denote input accepted]

theorem lower_runs {graph : Graph args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (emitted : lower graph entry input = some programs)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected := by
  obtain ⟨edited, accepted, rfl⟩ := Option.map_eq_some_iff.mp emitted
  refine ⟨lowerDiamond_run graph (some entry) input guard fuel initial, ?_⟩
  exact (lowerDiamond_run graph (some edited) input guard fuel initial).trans
    (congrArg (fun result : Word × Heap cells =>
      if fuel < 3 then none else
        let observed := graph.denote guard input result.2
        some (observed.1, Buffer.mk observed.2)) (rewrite_denote input accepted initial.cell))

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Proofs
