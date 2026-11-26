module

public import Silmaril.Formats.Parquet.Int96.Dictionary.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Int96.Dictionary.Wire

public section

namespace Silmaril.Formats.Parquet.Int96.Dictionary

/-- The leading dictionary re-encodes the exact original PLAIN words in entry
order. -/
theorem readDictionary_wire {limits : Limits} {policy : Policy} {source : Bytes}
    {frame : Parquet.Page.Frame} {dictionary : Array (Int96.Page.Value policy)}
    (h : readDictionary limits policy source frame = .ok dictionary) :
    ∃ (header : Parquet.Page.Dictionary) (entries : List Payload),
      frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧ frame.value.crc = none ∧
      frame.value.compressedSize = frame.value.uncompressedSize ∧
      header.numValues ≤ limits.maxEntries ∧ frame.value.compressedSize ≤ limits.maxDictionaryBytes ∧
      entries.length = header.numValues ∧
      (frameBody source frame).toList = entries.flatMap Payload.encode ∧
      dictionary = (entries.map (·.toTicks policy)).toArray :=
  Proofs.Formats.Parquet.Int96.Dictionary.readDictionary_wire h

/-- An invalid word reports the first bad dictionary entry in physical entry
order. -/
theorem readDictionary_entry_error {limits : Limits} {policy : Policy} {source : Bytes}
    {frame : Parquet.Page.Frame} {index : Nat}
    (h : readDictionary limits policy source frame = .error (.dictionaryEntry (.invalidWord index))) :
    ∃ header words before bad after,
      frame.value.kind = .dictionary header ∧
      Plain.decodeFixedLenBytes 12 header.numValues (frameBody source frame) = .ok words ∧
      words.map some = before ++ some bad :: after ∧
      (∃ entries, Int96.Page.decodeSlots 0 before = .ok entries) ∧
      Payload.decode? bad.toList = none ∧ index = before.length :=
  Proofs.Formats.Parquet.Int96.Dictionary.readDictionary_entry_error h

/-- Each logical slot preserves nulls or uses the referenced dictionary entry. -/
theorem selectSlots_ordered {α : Type} {dictionary : Array α} {start : Nat}
    {references : List (Option Nat)} {slots : List (Option α)}
    (h : selectSlots dictionary start references = .ok slots) :
    List.Forall₂ (SlotMatches dictionary) references slots :=
  Proofs.Formats.Parquet.Int96.Dictionary.selectSlots_ordered h

/-- A bad reference identifies the first failed lookup by its logical slot. -/
theorem selectSlots_reference_error {α : Type} {dictionary : Array α} {start : Nat}
    {references : List (Option Nat)} {slot index : Nat}
    (h : selectSlots dictionary start references = .error (.reference slot index)) :
    ∃ before after, references = before ++ some index :: after ∧ slot = start + before.length ∧
      dictionary[index]? = none ∧ ∃ prefixSlots, selectSlots dictionary start before = .ok prefixSlots :=
  Proofs.Formats.Parquet.Int96.Dictionary.selectSlots_reference_error h

/-- Both page versions preserve the checked mask, exact index stream and
ordered lookups. -/
theorem decodeData_wire {limits : Limits} {policy : Policy}
    {dictionary : Array (Int96.Page.Value policy)} {params : ScalarPage.Parameters} {body : Bytes}
    {slots : Slots policy} (h : decodeData limits dictionary params body = .ok slots) :
    ∃ layout prepared references raw, ∃ width : UInt8, ∃ runs : List UInt8,
      ScalarPage.validateFor 8 params limits.scalar body = .ok layout ∧
      ScalarPage.PreparedWire params limits.scalar layout body prepared ∧
      DictionaryIndex.readIndices limits.indices (prepared.mask.count true) prepared.scalars = .ok references ∧
      prepared.scalars.toList = width :: runs ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs references ∧
      raw.map Option.isSome = prepared.mask ∧ raw.filterMap id = references ∧
      List.Forall₂ (SlotMatches dictionary) raw slots ∧ slots.map Option.isSome = prepared.mask ∧
      slots.length = params.numValues :=
  Proofs.Formats.Parquet.Int96.Dictionary.decodeData_wire h

/-- The first missing reference's logical index counts all preceding nulls. -/
theorem decodeData_reference_error {limits : Limits} {policy : Policy}
    {dictionary : Array (Int96.Page.Value policy)} {params : ScalarPage.Parameters}
    {body : Bytes} {slot index : Nat}
    (h : decodeData limits dictionary params body = .error (.reference slot index)) :
    ∃ prepared references before after,
      ScalarPage.prepareFor 8 params limits.scalar body = .ok prepared ∧
      DictionaryIndex.readIndices limits.indices (prepared.mask.count true) prepared.scalars = .ok references ∧
      FlatPage.reconstruct prepared.mask references = .ok (before ++ some index :: after) ∧
      slot = before.length ∧ dictionary[index]? = none ∧
      ∃ prefixSlots, selectSlots dictionary 0 before = .ok prefixSlots :=
  Proofs.Formats.Parquet.Int96.Dictionary.decodeData_reference_error h

/-- One leading dictionary governs all data frames in the exact original chunk
order. -/
theorem read_wire {limits : Limits} {policy : Policy} {source : Bytes} {footerStart rowCount : Nat}
    {leaf : Footer.SchemaElement} {column : Footer.ColumnMetadata} {slots : Slots policy}
    (h : read limits policy source footerStart rowCount leaf column = .ok slots) :
    ∃ span first rest dictionary pages,
      Parquet.Page.columnSpan footerStart column = some span ∧
      Parquet.Page.Chain span span.start span.stop (first :: rest) ∧
      column.dictionaryPageOffset = some (first.header.start : Int) ∧
      rest.head?.map (fun frame => (frame.header.start : Int)) = some column.dataPageOffset ∧
      readDictionary limits policy source first = .ok dictionary ∧
      List.Forall₂ (fun frame page => ∃ params, dataParameters leaf frame.value = .ok params ∧
        decodeData limits dictionary params (frameBody source frame) = .ok page) rest pages ∧
      slots = pages.flatten ∧ slots.length = rowCount :=
  Proofs.Formats.Parquet.Int96.Dictionary.read_wire h

/-- The wire witness includes the exact frames returned by the checked chunk
parser on the original source. -/
theorem read_framed_wire {limits : Limits} {policy : Policy} {source : Bytes} {footerStart rowCount : Nat}
    {leaf : Footer.SchemaElement} {column : Footer.ColumnMetadata} {slots : Slots policy}
    (h : read limits policy source footerStart rowCount leaf column = .ok slots) :
    ∃ span first rest dictionary pages,
      Parquet.Page.columnSpan footerStart column = some span ∧
      Parquet.Page.readChunk limits.framing source span = .ok (first :: rest) ∧
      Parquet.Page.Chain span span.start span.stop (first :: rest) ∧
      column.dictionaryPageOffset = some (first.header.start : Int) ∧
      rest.head?.map (fun frame => (frame.header.start : Int)) = some column.dataPageOffset ∧
      readDictionary limits policy source first = .ok dictionary ∧
      List.Forall₂ (fun frame page => ∃ params, dataParameters leaf frame.value = .ok params ∧
        decodeData limits dictionary params (frameBody source frame) = .ok page) rest pages ∧
      slots = pages.flatten ∧ slots.length = rowCount :=
  Proofs.Formats.Parquet.Int96.Dictionary.read_framed_wire h

end Silmaril.Formats.Parquet.Int96.Dictionary
