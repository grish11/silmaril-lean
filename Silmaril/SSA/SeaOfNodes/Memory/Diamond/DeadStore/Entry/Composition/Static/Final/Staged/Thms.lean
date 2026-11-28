module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Staged.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Staged.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Staged

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (entryDestination run)
open Retained.Load.Static
open Retained.Load.Static.Sequence.Search

variable {args : List ValueSort} {cells : Nat}
variable {graph : Graph args} {entry : Memory.Graph args} {input : Tuple (Val cells) args}
variable {result : Staged.Result cells args}

/-- Discovery succeeds at exactly the version admitted by the existing
final-Store cut. -/
theorem find_eq_some_iff (entry : Memory.Graph args) (version : Nat) :
    find entry = some version ↔ ∃ store retained, Final.cut version entry = some (store, retained) :=
  Proofs.find_eq_some_iff entry version

theorem find_none_iff (entry : Memory.Graph args) :
    find entry = none ↔ ∀ version, Final.cut version entry = none :=
  Proofs.find_none_iff entry

/-- The inferred entry contracts validate at every typed input. -/
theorem lower_eq_ok (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args) :
    let found := discover entry (Inference.inferContracts entry)
    let stage : Emission cells args := ⟨found, Entry.lowerPair graph entry found.entry input⟩
    lower graph entry input = .ok ⟨stage, checkRoutes cells graph stage.entry⟩ :=
  Proofs.lower_eq_ok graph entry input

/-- Replay the exact entry plan and check the reported route outcome on
the residual table. On success the intermediate emitted artifacts agree. -/
theorem lower_checked (emitted : lower graph entry input = .ok result) :
    Inference.lower graph entry input = .ok result.entryOnly ∧
      Sequence.lower graph entry result.entryOnly.plan input = some result.entryOnly.programs ∧
      match result.route with
      | .noFinalCandidate => find result.entryOnly.entry = none
      | .routesRefused version =>
        find result.entryOnly.entry = some version ∧ Final.lower cells graph result.entryOnly.entry version = none
      | .applied version artifacts =>
        find result.entryOnly.entry = some version ∧ Final.lower cells graph result.entryOnly.entry version = some artifacts ∧
          artifacts.original = result.entryOnly.programs.optimized :=
  Proofs.lower_checked emitted

/-- The original and final emitted CFGs agree on the entry packet, word
and whole final buffer for either predicate and every CF budget. -/
theorem lower_observations (emitted : lower graph entry input = .ok result)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := result.programs
    let observed := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (observed.1, Buffer.mk observed.2)
    entryDestination programs.optimized programs.input guard initial =
      entryDestination programs.original programs.input guard initial ∧
      run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lower_observations emitted guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Staged
