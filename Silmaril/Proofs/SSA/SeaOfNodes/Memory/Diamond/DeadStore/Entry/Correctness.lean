module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Defs
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Proofs

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.DeadStore.Search.Selection (Result storeVersions)
open Memory.DeadStore.Search.Selection.Readers renaming discover → discoverReaders
open Memory.DeadStore.Search.Selection.Readers.Repeat renaming rewrite_denote → repeatDenote
open Discovery.MemRef.CF (Programs entryTransition lowerDiamond lowerDiamond_entryTransition lowerDiamond_run run)

variable {args : List ValueSort} {cells : Nat}
variable {entry edited : Memory.Graph args}

private theorem checked_denote {candidate : Memory.DeadStore.Candidate}
    {facts : Memory.Forwarding.Disjoint.Certificate args} (input : Tuple (Val cells) args)
    (accepted : Memory.DeadStore.rewrite entry candidate facts input = some edited)
    (initial : Heap cells) : edited.denote input initial = entry.denote input initial := by
  obtain ⟨structural, valid⟩ := (Memory.DeadStore.rewrite_eq_some_iff input).mp accepted
  exact Memory.DeadStore.rewriteWith_denote structural input valid initial

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
  exact checked_denote input checked initial

theorem rewriteSelected_checked {removeVersion : Nat} {result : Result args}
    (input : Tuple (Val cells) args) (accepted : rewriteSelected entry removeVersion input = some result) :
    result.candidate.removeVersion = removeVersion ∧
      discoverReaders entry removeVersion = some result.facts ∧
      Memory.DeadStore.Search.discover entry removeVersion result.facts = some result.candidate ∧
      Memory.DeadStore.rewrite entry result.candidate result.facts input = some result.graph := by
  obtain ⟨facts, readers, tried⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨candidate, found, checked⟩ := Option.bind_eq_some_iff.mp tried
  obtain ⟨edited, rewritten, packed⟩ := Option.bind_eq_some_iff.mp checked
  cases Option.some.inj packed
  exact ⟨(Memory.DeadStore.Search.discover_sound found).1, readers, found, rewritten⟩

theorem rewriteSelected_denote {removeVersion : Nat} {result : Result args}
    (input : Tuple (Val cells) args) (accepted : rewriteSelected entry removeVersion input = some result)
    (initial : Heap cells) : result.graph.denote input initial = entry.denote input initial :=
  checked_denote input (rewriteSelected_checked input accepted).2.2.2 initial

private theorem lowerPair_entryTransition_eq (graph : Graph args) (input : Tuple (Val cells) args)
    (guard : Bool) (initial : Buffer cells) (same : edited.denote input initial.cell = entry.denote input initial.cell) :
    let programs := lowerPair graph entry edited input
    entryTransition programs.optimized programs.input guard initial =
      entryTransition programs.original programs.input guard initial := by
  change entryTransition (lowerDiamond cells graph (some edited)) input guard initial =
    entryTransition (lowerDiamond cells graph (some entry)) input guard initial
  rw [lowerDiamond_entryTransition, lowerDiamond_entryTransition]
  simp only [same]

theorem lower_entryTransition_eq {graph : Graph args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (emitted : lower graph entry input = some programs)
    (guard : Bool) (initial : Buffer cells) :
    entryTransition programs.optimized programs.input guard initial =
      entryTransition programs.original programs.input guard initial := by
  obtain ⟨edited, accepted, rfl⟩ := Option.map_eq_some_iff.mp emitted
  exact lowerPair_entryTransition_eq graph input guard initial (rewrite_denote input accepted initial.cell)

theorem lowerSelected_entryTransition_eq {graph : Graph args} {programs : Programs cells args} {removeVersion : Nat}
    (input : Tuple (Val cells) args) (emitted : lowerSelected graph entry removeVersion input = some programs)
    (guard : Bool) (initial : Buffer cells) :
    entryTransition programs.optimized programs.input guard initial =
      entryTransition programs.original programs.input guard initial := by
  obtain ⟨result, accepted, rfl⟩ := Option.map_eq_some_iff.mp emitted
  exact lowerPair_entryTransition_eq graph input guard initial (rewriteSelected_denote input accepted initial.cell)

private theorem lowerPair_runs (graph : Graph args) (input : Tuple (Val cells) args)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells)
    (same : edited.denote input initial.cell = entry.denote input initial.cell) :
    let programs := lowerPair graph entry edited input
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected := by
  refine ⟨lowerDiamond_run graph (some entry) input guard fuel initial, ?_⟩
  exact (lowerDiamond_run graph (some edited) input guard fuel initial).trans
    (congrArg (fun result : Word × Heap cells =>
      if fuel < 3 then none else
        let observed := graph.denote guard input result.2
        some (observed.1, Buffer.mk observed.2)) same)

theorem lower_runs {graph : Graph args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (emitted : lower graph entry input = some programs)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected := by
  obtain ⟨edited, accepted, rfl⟩ := Option.map_eq_some_iff.mp emitted
  exact lowerPair_runs graph input guard fuel initial (rewrite_denote input accepted initial.cell)

theorem lowerSelected_runs {graph : Graph args} {programs : Programs cells args} {removeVersion : Nat}
    (input : Tuple (Val cells) args) (emitted : lowerSelected graph entry removeVersion input = some programs)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected := by
  obtain ⟨result, accepted, rfl⟩ := Option.map_eq_some_iff.mp emitted
  exact lowerPair_runs graph input guard fuel initial (rewriteSelected_denote input accepted initial.cell)

theorem lowerRepeated_entryTransition_eq (graph : Graph args) (entry : Memory.Graph args)
    (input : Tuple (Val cells) args) (guard : Bool) (initial : Buffer cells) :
    let programs := (lowerRepeated graph entry input).programs
    entryTransition programs.optimized programs.input guard initial =
      entryTransition programs.original programs.input guard initial :=
  lowerPair_entryTransition_eq graph input guard initial (repeatDenote entry input initial.cell)

theorem lowerRepeated_runs (graph : Graph args) (entry : Memory.Graph args)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lowerRepeated graph entry input).programs
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  lowerPair_runs graph input guard fuel initial (repeatDenote entry input initial.cell)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Proofs
