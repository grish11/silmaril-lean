module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.Defs
import Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.Correctness

/-! Exact original frames, delta-length slots and positional row pairing. -/

public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength

theorem openFile_snapshot {limits : Limits} {input : Bytes} {int32Name byteArrayName : String}
    {checked : Checked int32Name byteArrayName} (opened : openFile limits input int32Name byteArrayName = .ok checked) :
    Snapshot.check (Failure := Unit) limits.group.snapshot input = .ok checked.snapshot ∧
    checked.snapshot.metadata.schema[checked.int32Binding.leafOrdinal]? = some checked.int32Binding.leaf ∧
    checked.snapshot.metadata.schema[checked.byteArrayBinding.leafOrdinal]? = some checked.byteArrayBinding.leaf :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.openFile_snapshot opened

/-- Each ordered binary frame consumes precisely its delta lengths and opaque
payload, yielding one reconstructed slot list for that frame. -/
theorem readBinary_wire {int32Name byteArrayName : String} {checked : Checked int32Name byteArrayName}
    {limits : Limits} {index : Nat} {slots : List (Option Bytes)}
    (read : readBinary checked limits index = .ok slots) : ∃ group, BinaryWire checked limits index group slots :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.readBinary_wire read

/-- Successful column reads agree on the footer count and yield one pair per row. -/
theorem readGroup_of_columns {int32Name byteArrayName : String} {checked : Checked int32Name byteArrayName}
    {limits : Limits} {index : Nat} {integers : List (Option Int32)} {bytes : List (Option Bytes)}
    (readInts : checked.readInt32 limits.group index = .ok integers)
    (readBytes : readBinary checked limits index = .ok bytes) :
    integers.length = bytes.length ∧ readGroup checked limits index = .ok (integers.zip bytes) :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.readGroup_of_columns readInts readBytes

/-- Unzipping the successful pairs recovers both complete checked lists. -/
theorem readGroup_wire {int32Name byteArrayName : String} {checked : Checked int32Name byteArrayName}
    {limits : Limits} {index : Nat} {rows : List Int32ByteArrayGroup.Row}
    (read : readGroup checked limits index = .ok rows) : GroupWire checked limits index rows :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.readGroup_wire read

theorem readGroup_int32_error {int32Name byteArrayName : String} {checked : Checked int32Name byteArrayName}
    {limits : Limits} {index : Nat} {reason : FlatColumn.Error FlatScan.AdapterError}
    (failed : checked.readInt32 limits.group index = .error reason) :
    readGroup checked limits index = .error (.int32 reason) := by
  simp [readGroup, failed]

theorem readGroup_byteArray_error {int32Name byteArrayName : String} {checked : Checked int32Name byteArrayName}
    {limits : Limits} {index : Nat} {integers : List (Option Int32)} {reason : FlatColumn.Error PageError}
    (earlier : checked.readInt32 limits.group index = .ok integers)
    (failed : readBinary checked limits index = .error reason) :
    readGroup checked limits index = .error (.byteArray reason) := by
  simp [readGroup, earlier, failed]

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength
