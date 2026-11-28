module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search

open RVSDG (Tuple)
open Memory.DeadStore.Search.Selection (storeVersions)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF renaming run → runCF
open Discovery.MemRef.CF (entryTransition)

variable {args : List ValueSort} {cells : Nat}
variable {entry : Memory.Graph args} {contracts : List (AddressContract args)}

theorem checkContracts_iff_valid (contracts : List (AddressContract args)) (input : Tuple (Val cells) args) :
    checkContracts contracts input = true ↔ ContractsValid contracts input :=
  Proofs.checkContracts_iff_valid contracts input

theorem find_checked {step : Step args} {retained : Memory.Graph args}
    (accepted : find entry contracts = some (step, retained)) :
    step.version ∈ storeVersions entry ∧ step.facts ∈ contracts ∧
      ∃ selected, Static.cut step.facts step.version entry = some (selected, retained) :=
  Proofs.find_checked accepted

theorem find_none_iff (entry : Memory.Graph args) (contracts : List (AddressContract args)) :
    find entry contracts = none ↔
      ∀ version ∈ storeVersions entry, ∀ facts ∈ contracts, Static.cut facts version entry = none :=
  Proofs.find_none_iff entry contracts

/-- Every generated plan step replays in the existing checker and uses
one of the supplied contracts. -/
theorem discover_replays (entry : Memory.Graph args) (contracts : List (AddressContract args)) :
    let result := discover entry contracts
    result.plan.rewrite entry = some result.entry ∧ ∀ step ∈ result.plan, step.facts ∈ contracts :=
  Proofs.discover_replays entry contracts

/-- At a satisfying invocation, the Store count suffices to exhaust the
eligible cuts on the final table under the supplied contracts. -/
theorem discover_exhausted (input : Tuple (Val cells) args) (valid : ContractsValid contracts input) :
    ∀ version ∈ storeVersions (discover entry contracts).entry,
      ∀ facts ∈ contracts, Static.cut facts version (discover entry contracts).entry = none :=
  Proofs.discover_exhausted input valid

theorem lower_error_iff (graph : Graph args) (entry : Memory.Graph args) (contracts : List (AddressContract args))
    (input : Tuple (Val cells) args) :
    lower graph entry contracts input = .error .invalidContracts ↔ ¬ ContractsValid contracts input :=
  Proofs.lower_error_iff graph entry contracts input

/-- Successful emission is the exact replayed program pair, and the
final table admits no further cut under the supplied contracts. -/
theorem lower_checked {graph : Graph args} {input : Tuple (Val cells) args} {emission : Emission cells args}
    (emitted : lower graph entry contracts input = .ok emission) :
    Sequence.lower graph entry emission.plan input = some emission.programs ∧
      ∀ version ∈ storeVersions emission.entry, ∀ facts ∈ contracts, Static.cut facts version emission.entry = none :=
  Proofs.lower_checked emitted

/-- The emitted CFGs agree on the successor packet, returned word and
whole entry and final buffers for either predicate and every CF budget. -/
theorem lower_observations {graph : Graph args} {input : Tuple (Val cells) args} {emission : Emission cells args}
    (emitted : lower graph entry contracts input = .ok emission) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := emission.programs
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    entryTransition programs.optimized programs.input guard initial =
      entryTransition programs.original programs.input guard initial ∧
      runCF programs.original programs.input guard fuel initial = expected ∧
      runCF programs.optimized programs.input guard fuel initial = expected := by
  have replay := (lower_checked emitted).1
  exact ⟨Sequence.lower_entryTransition_eq replay guard initial, Sequence.lower_runs replay guard fuel initial⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search
