module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Staged.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Staged.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Staged

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (entryDestination run)
open Retained.Load.Static
open Retained.Load.Static.Sequence.Search

variable {args : List ValueSort} {cells : Nat}
variable {graph : Graph args} {entry : Memory.Graph args} {input : Tuple (Val cells) args}
variable {result : Staged.Result cells args}

/-- Every typed valuation validates the inferred entry contracts. -/
theorem lower_eq_ok (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args) :
    let found := discover entry (Inference.inferContracts entry)
    let stage : Emission cells args := ⟨found, Entry.lowerPair graph entry found.entry input⟩
    lower graph entry input = .ok ⟨stage, checkRoutes cells graph stage.entry⟩ :=
  Proofs.lower_eq_ok graph entry input

/-- Replay the discovered entry plan and check the reported route outcome
against its exact residual table. An applied cut starts from the exact
optimized artifact of the entry stage. -/
theorem lower_checked (emitted : lower graph entry input = .ok result) :
    Inference.lower graph entry input = .ok result.entryOnly ∧
      Sequence.lower graph entry result.entryOnly.plan input = some result.entryOnly.programs ∧
      match result.route with
      | .entryNotSingleton => Composition.asPrefixStore result.entryOnly.entry = none
      | .routesRefused =>
        (Composition.asPrefixStore result.entryOnly.entry).isSome = true ∧
          Static.lower cells graph result.entryOnly.entry = none
      | .applied artifacts =>
        Static.lower cells graph result.entryOnly.entry = some artifacts ∧
          artifacts.original = result.entryOnly.programs.optimized :=
  Proofs.lower_checked emitted

/-- The original and final CFGs agree on the entry successor packet and
on the returned word and entire final buffer at every CF budget. -/
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

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Staged
