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
  Proofs.Formats.Parquet.ByteArrayFallback.readDictionary_wire (profile := .rleDictionary) h

/-- The original frame selects the PLAIN or dictionary interpretation and
retains the exact definition mask, value order and declared count. -/
theorem decodeData_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {dictionary : Option (Array Bytes)} {frame : Page.Frame} {slots : List (Option Bytes)}
    (h : decodeData limits metadata source dictionary frame = .ok slots) : PageWire limits source dictionary frame slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.decodeData_wire (profile := .rleDictionary) h

/-- A successful selected read uses its own snapshot, chunk and leading
dictionary. The result concatenates one slot list per data frame in wire order. -/
theorem readGroup_wire {name : String} {checked : Checked name} {limits : Limits}
    {index : Nat} {slots : List (Option Bytes)} (h : readGroup checked limits index = .ok slots) :
    GroupWire checked limits index slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.readGroup_wire (profile := .rleDictionary) h

/-- The original V1 header keeps its value encoding and row count. The
RLE definition tag is preserved and only the absent repetition tag changes. -/
theorem legacy_parameters_wire {header : Page.Header} {params : ScalarPage.Parameters}
    (admitted : Profile.plainDictionaryV1.parameters header = some params) :
    ∃ raw, FlatColumn.pageParameters .optional 0 header = some raw ∧
      raw.version = .v1 3 4 ∧ params = { raw with version := .v1 3 3 } :=
  Proofs.Formats.Parquet.ByteArrayFallback.legacy_parameters_wire admitted

/-- The legacy reader retains the same-snapshot wire relation for a leading
tag-2 dictionary and original V1 tag-2 or PLAIN data pages. -/
theorem readLegacyGroup_wire {name : String} {checked : Checked name} {limits : Limits}
    {index : Nat} {slots : List (Option Bytes)}
    (h : readLegacyGroup checked limits index = .ok slots) :
    GroupWireFor .plainDictionaryV1 checked limits index slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.readGroup_wire (profile := .plainDictionaryV1) h

/-- The legacy walk can reuse a BYTE_ARRAY binding from a paired checked
snapshot, preserving its original leaf, chunk, frames and slot count. -/
theorem readBoundLegacyGroup_wire {snapshot : Snapshot.Checked} {name : String}
    {binding : FlatColumn.Binding snapshot ⟨name, .byteArray, .optional⟩}
    {limits : Limits} {index : Nat} {slots : List (Option Bytes)}
    (read : readBoundGroupFor .plainDictionaryV1 binding limits index = .ok slots) :
    ∃ group, BoundGroupWireFor .plainDictionaryV1 binding limits index group slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.readBoundGroup_wire read

end Silmaril.Formats.Parquet.ByteArrayFallback
