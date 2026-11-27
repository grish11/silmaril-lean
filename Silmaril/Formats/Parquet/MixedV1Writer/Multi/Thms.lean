module

public import Silmaril.Formats.Parquet.MixedV1Writer.Multi.Defs
import Silmaril.Proofs.Formats.Parquet.MixedV1Writer.Multi.Correctness

public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.Multi

/-- Successful emission checks aggregate limits, layout, the full footer and every actual page window. -/
theorem emit_checked {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    input.groups ≠ [] ∧ input.groups.length ≤ limits.maxGroups ∧
    input.totalRows ≤ limits.maxTotalRows ∧ input.Matches limits ∧ output.Checked limits input ∧
    certify limits input output = .ok () :=
  Proofs.Formats.Parquet.MixedV1Writer.Multi.emit_checked written

/-- Every input group is recovered at its original footer ordinal, with the exact paired slots
and the corresponding checked wire chunks. -/
theorem emit_indexed {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    ∃ opened : Int32ByteArrayGroup.Checked input.intField input.byteField,
      Int32ByteArrayGroup.openFile limits.writer.readback output.bytes input.intField input.byteField = .ok opened ∧
      opened.snapshot.groupCount = input.groups.length ∧
      ∀ i : Fin input.groups.length,
        opened.readGroup limits.writer.readback i.val = .ok (input.groups.get i).rows ∧
        Int32ByteArrayGroup.GroupWire opened limits.writer.readback i.val (input.groups.get i).rows :=
  Proofs.Formats.Parquet.MixedV1Writer.Multi.emit_indexed written

/-- A zero-row input group is present and reads as an empty list at its original ordinal. -/
theorem emit_empty {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) (i : Fin input.groups.length)
    (empty : (input.groups.get i).rowCount = 0) :
    ∃ opened : Int32ByteArrayGroup.Checked input.intField input.byteField,
      Int32ByteArrayGroup.openFile limits.writer.readback output.bytes input.intField input.byteField = .ok opened ∧
      opened.readGroup limits.writer.readback i.val = .ok [] :=
  Proofs.Formats.Parquet.MixedV1Writer.Multi.emit_empty written i empty

end Silmaril.Formats.Parquet.MixedV1Writer.Multi
