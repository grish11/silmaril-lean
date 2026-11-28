module

public import Silmaril.SSA.SeaOfNodes.Memory.AddressProvenance.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.AddressProvenance.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.AddressProvenance

open RVSDG (Locals Origin Tuple)
open Memory.DeadStore.Search.Selection.Readers.Repeat (operations)

variable {args : List ValueSort} {past : List (List ValueSort)} {cells : Nat}

/-- A reachable memory scope has only word-valued bindings, so each typed
address origin is an original argument. -/
theorem LoadScope.address_argument (scope : LoadScope past) (wire : Origin args past .address) :
    ∃ port, wire = .arg port :=
  Proofs.address_argument scope wire

/-- The same argument fixes the cell at every local state for a fixed input. -/
theorem LoadScope.read_address (scope : LoadScope past) (wire : Origin args past .address) :
    ∃ port, wire = .arg port ∧
      ∀ (input : Tuple (Val cells) args) (locals : Locals (Val cells) past),
        readValue wire input locals = input.get port := by
  obtain ⟨port, rfl⟩ := scope.address_argument wire
  exact ⟨port, rfl, fun _ _ => rfl⟩

/-- Every actual Load and Store in an ordered native graph uses an
original address argument, including accesses after an arbitrary prefix. -/
theorem graph_operations_argument_addresses (graph : Graph args) :
    ∀ operation ∈ operations graph, ArgumentAddress operation :=
  Proofs.operations_argument_addresses graph .start

end Silmaril.SSA.SeaOfNodes.Memory.AddressProvenance
