module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static

open RVSDG (Port Tuple)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Discovery.MemRef.CF (entryTransition run)
open Silmaril.MLIR.MemRef (Buffer)

variable {args : List ValueSort} {cells : Nat}
variable {facts : AddressContract args} {input : Tuple (Val cells) args}

/-- The optional invocation check validates exactly the stated address facts. -/
theorem AddressContract.check_iff_valid (facts : AddressContract args) (input : Tuple (Val cells) args) :
    facts.check input = true ↔ facts.Valid input :=
  Proofs.check_iff_valid facts input

/-- An accepted static cut reproduces the concrete cut at every satisfying input.
The version and retained graph depend only on the table and address facts. -/
theorem cut_agrees {entry retained : Memory.Graph args} {selected : PrefixStore args} {version : Nat}
    (accepted : cut facts version entry = some (selected, retained)) (valid : facts.Valid input) :
    Load.cutOverwrite version input entry = some (selected, retained) :=
  Proofs.cut_agrees accepted valid

theorem cut_preserves {entry retained : Memory.Graph args} {selected : PrefixStore args} {version : Nat}
    (accepted : cut facts version entry = some (selected, retained)) (valid : facts.Valid input)
    (initial : Heap cells) :
    DeletesStores 1 (operations entry) (operations retained) ∧
      entry.denote input initial = retained.denote input initial := by
  obtain ⟨order, same⟩ := Load.cutOverwrite_preserves input (cut_agrees accepted valid)
  exact ⟨order, same PUnit.unit initial⟩

/-- Both emitted entries forward the same successor packet and entire buffer. -/
theorem lower_entryTransition_eq (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (prior : Option (Memory.DeadStore.Candidate × Port args .address))
    (valid : facts.Valid input) (guard : Bool) (initial : Buffer cells) :
    let programs := lower cells graph entry version facts prior
    entryTransition programs.optimized input guard initial = entryTransition programs.original input guard initial :=
  Proofs.lower_entryTransition_eq graph entry version prior valid guard initial

/-- The fixed emitted pair agrees for every satisfying valuation, either
predicate and every initial buffer and CF budget. Three CF steps suffice. -/
theorem lower_runs (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (prior : Option (Memory.DeadStore.Candidate × Port args .address))
    (valid : facts.Valid input) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := lower cells graph entry version facts prior
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original input guard fuel initial = expected ∧
      run programs.optimized input guard fuel initial = expected :=
  Proofs.lower_runs graph entry version prior valid guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static
