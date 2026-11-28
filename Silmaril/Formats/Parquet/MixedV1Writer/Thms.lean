module

public import Silmaril.Formats.Parquet.MixedV1Writer.Defs
import Silmaril.Proofs.Formats.Parquet.MixedV1Writer.Correctness

public section

namespace Silmaril.Formats.Parquet.MixedV1Writer

/-- Successful emission checks the exact footer, both absolute page spans and their bodies.
The existing mixed reader returns exactly the input pairs. -/
theorem emit_checked {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    input.Valid limits ∧ output.Checked limits input ∧
    readback limits.readback input output = .ok input.rows :=
  Proofs.Formats.Parquet.MixedV1Writer.emit_checked written

/-- Valid input pairs both complete slot lists without dropping a position. -/
theorem rows_exact {input : Input} {limits : Limits} (valid : input.Valid limits) :
    input.rows.length = input.rowCount ∧ input.rows.map Prod.fst = input.integers.slots ∧
      input.rows.map Prod.snd = input.octets.slots :=
  Proofs.Formats.Parquet.MixedV1Writer.rows_exact valid

/-- The checked mixed reader ties every returned row to the two original chunks at footer ordinal zero. -/
theorem emit_wire {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    ∃ opened : Int32ByteArrayGroup.Checked input.intField input.byteField,
      Int32ByteArrayGroup.openFile limits.readback output.bytes input.intField input.byteField = .ok opened ∧
      Int32ByteArrayGroup.GroupWire opened limits.readback 0 input.rows :=
  Proofs.Formats.Parquet.MixedV1Writer.emit_wire written

end Silmaril.Formats.Parquet.MixedV1Writer
