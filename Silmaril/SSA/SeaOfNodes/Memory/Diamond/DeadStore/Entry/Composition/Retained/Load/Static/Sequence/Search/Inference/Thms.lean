module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Inference.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Inference

open RVSDG (Tuple)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.Forwarding.Disjoint (Certificate)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF renaming run → runCF
open Discovery.MemRef.CF (entryTransition)

variable {args : List ValueSort} {cells : Nat}
variable {graph : Graph args} {entry : Memory.Graph args} {input : Tuple (Val cells) args}
variable {emission : Search.Emission cells args}

/-- Inference needs only typed Store operands. Every valuation satisfies
the generated contracts. -/
theorem inferContracts_valid (entry : Memory.Graph args) (input : Tuple (Val cells) args) :
    Search.ContractsValid (inferContracts entry) input := by
  intro facts member
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
  simp [AddressContract.Valid, Certificate.Valid]

/-- Inferred contracts always pass invocation validation. The existing
finder and emitter supply the resulting plan and programs. -/
theorem lower_eq_ok (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args) :
    let result := Search.discover entry (inferContracts entry)
    lower graph entry input = .ok ⟨result, Entry.lowerPair graph entry result.entry input⟩ := by
  have valid := (Search.checkContracts_iff_valid _ input).mpr (inferContracts_valid entry input)
  simp [lower, Search.lower, valid]

/-- The emitted pair replays through the explicit plan API. Exhaustion
ranges over the inferred contracts on the final table. -/
theorem lower_checked (emitted : lower graph entry input = .ok emission) :
    Sequence.lower graph entry emission.plan input = some emission.programs ∧
      ∀ version ∈ storeVersions emission.entry,
        ∀ facts ∈ inferContracts entry, Static.cut facts version emission.entry = none :=
  Search.lower_checked emitted

/-- Original and optimized CFG observations agree for either predicate,
every initialized buffer and every CF budget. -/
theorem lower_observations (emitted : lower graph entry input = .ok emission)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := emission.programs
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    entryTransition programs.optimized programs.input guard initial =
      entryTransition programs.original programs.input guard initial ∧
      runCF programs.original programs.input guard fuel initial = expected ∧
      runCF programs.optimized programs.input guard fuel initial = expected :=
  Search.lower_observations emitted guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Inference
