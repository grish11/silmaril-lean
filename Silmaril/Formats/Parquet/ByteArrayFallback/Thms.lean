module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Defs
import Silmaril.Formats.Parquet.Plain.ByteArray.File.Thms
import Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Wire

/-! Same-snapshot binding, original dictionary entries and ordered data-page slots. -/

public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback

theorem openFile_wire {limits : Limits} {input : Bytes} {name : String} {checked : Checked name}
    (opened : openFile limits input name = .ok checked) :
    Snapshot.check (Failure := Unit) limits.file.snapshot input = .ok checked.snapshot ∧
    input.length ≤ limits.file.maxFileBytes ∧ checked.snapshot.metadata.numRows.toNat ≤ limits.file.maxFileRows ∧
    checked.snapshot.metadata.schema[checked.binding.leafOrdinal]? = some checked.binding.leaf ∧
    checked.binding.leaf.name = name ∧ checked.binding.leaf.physicalType = some .byteArray ∧
    checked.binding.leaf.repetition = some FlatColumn.Layout.optional.repetition :=
  Plain.ByteArray.File.openFile_wire opened

/-- Exact PLAIN entry bytes and typed entries in the original dictionary order. -/
theorem readDictionary_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {frame : Page.Frame} {entries : Array Bytes}
    (h : readDictionary limits metadata source frame = .ok entries) : DictionaryWire limits source frame entries :=
  Proofs.Formats.Parquet.ByteArrayFallback.readDictionary_wire h

/-- The original frame selects the PLAIN or dictionary interpretation and
retains the exact definition mask, value order and declared count. -/
theorem decodeData_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {dictionary : Option (Array Bytes)} {frame : Page.Frame} {slots : List (Option Bytes)}
    (h : decodeData limits metadata source dictionary frame = .ok slots) : PageWire limits source dictionary frame slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.decodeData_wire h

/-- A successful selected read uses its own snapshot, chunk and leading
dictionary. The result concatenates one slot list per data frame in wire order. -/
theorem readGroup_wire {name : String} {checked : Checked name} {limits : Limits}
    {index : Nat} {slots : List (Option Bytes)} (h : readGroup checked limits index = .ok slots) :
    GroupWire checked limits index slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.readGroup_wire h

end Silmaril.Formats.Parquet.ByteArrayFallback
