module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.DeadStore.Search.Selection.Readers renaming discover → discoverReaders
open Discovery.MemRef.CF (Programs entryTransition run)

variable {args : List ValueSort} {cells : Nat}
variable {entry edited : Memory.Graph args}

/-- A successful edit is precisely a checked deletion of Store 1 using
Store 2 as its overwrite, with inferred reader obligations. -/
theorem rewrite_checked (input : Tuple (Val cells) args) (accepted : rewrite entry input = some edited) :
    (storeVersions entry).length = 2 ∧
      ∃ facts, discoverReaders entry 1 = some facts ∧
        Memory.DeadStore.rewrite entry ⟨1, 2⟩ facts input = some edited :=
  Proofs.rewrite_checked input accepted

theorem rewrite_denote (input : Tuple (Val cells) args) (accepted : rewrite entry input = some edited)
    (initial : Heap cells) : edited.denote input initial = entry.denote input initial :=
  Proofs.rewrite_denote input accepted initial

/-- Both emitted entries agree on the actual successor frame and entire buffer. -/
theorem lower_entryTransition_eq {graph : Graph args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (emitted : lower graph entry input = some programs)
    (guard : Bool) (initial : Buffer cells) :
    entryTransition programs.optimized programs.input guard initial =
      entryTransition programs.original programs.input guard initial :=
  Proofs.lower_entryTransition_eq input emitted guard initial

/-- The entry edit preserves the word and whole final buffer for either
predicate. Each artifact still executes entry, one arm, and the join. -/
theorem lower_runs {graph : Graph args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (emitted : lower graph entry input = some programs)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lower_runs input emitted guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry
