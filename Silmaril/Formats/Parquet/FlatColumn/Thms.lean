module

public import Silmaril.Formats.Parquet.FlatColumn.Defs
import Silmaril.Proofs.Formats.Parquet.FlatColumn.Wire

/-! Selected leaf and chunk ordinals, frame order and exact callback inputs. -/

public section

namespace Silmaril.Formats.Parquet.FlatColumn

theorem binding_leaf {snapshot : Snapshot.Checked} {selection : Selection}
    (binding : Binding snapshot selection) :
    snapshot.metadata.schema[binding.leafOrdinal]? = some binding.leaf ∧
    binding.leaf.name = selection.name ∧ binding.leaf.physicalType = some selection.physical ∧
    binding.leaf.repetition = some selection.layout.repetition :=
  ⟨binding.leafAt, binding.leafName, binding.leafPhysical, binding.leafRepetition⟩

/-- The original page parse and body-slice callback results occur in wire order,
and the flattened callback slots have the footer row count. -/
theorem readColumn_wire {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {policy : Policy} {decode : DecodePage α ε}
    {index : Nat} {slots : List (Option α)} (read : readColumn binding limits policy decode index = .ok slots) :
    ∃ group, ColumnWire binding limits decode index group slots :=
  Proofs.Formats.Parquet.FlatColumn.readColumn_wire read

end Silmaril.Formats.Parquet.FlatColumn
