module

public import Silmaril.Formats.Parquet.DictionaryChunk.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.DictionaryChunk.Correctness

/-! Admission, exact payload bounds, and ordered slots for dictionary chunks. -/

public section

namespace Silmaril.Formats.Parquet.DictionaryChunk

/-- Framing preserves wire order, with at most one leading typed dictionary
at the declared offset and every dictionary-coded data page referring to it. -/
theorem read_admitted {limits : Limits} {source : Bytes} {footerStart rowCount : Nat}
    {field : FlatScan.Field} {column : Footer.ColumnMetadata} {chunk : Chunk}
    (parsed : read limits source footerStart field rowCount column = .ok chunk) :
    Admitted limits source footerStart rowCount field.layout column chunk :=
  Proofs.Formats.Parquet.DictionaryChunk.read_admitted parsed

/-- Every returned frame selects exactly its advertised payload inside the chunk. -/
theorem read_payloads {limits : Limits} {source : Bytes} {footerStart rowCount : Nat}
    {field : FlatScan.Field} {column : Footer.ColumnMetadata} {chunk : Chunk}
    (parsed : read limits source footerStart field rowCount column = .ok chunk) :
    ∀ frame ∈ chunk.frames, Page.FrameWithin chunk.span frame.header.start frame ∧
      (body source frame).length = frame.value.compressedSize :=
  Proofs.Formats.Parquet.DictionaryChunk.read_payloads parsed

/-- Column slots concatenate the decoded page slots in wire order, using the
same typed dictionary throughout. The row count and requiredness are checked. -/
theorem scanColumn_ordered {limits : Limits} {source : Bytes} {footerStart rowCount : Nat}
    {field : FlatScan.Field} {column : Footer.ColumnMetadata} {slots : List (Option Int32)}
    (decoded : scanColumn limits source footerStart field rowCount column = .ok slots) :
    ∃ chunk pages,
      read limits source footerStart field rowCount column = .ok chunk ∧
      List.Forall₂ (DataPage.Decodes limits source chunk.dictionary) chunk.data pages ∧
      slots = pages.flatten ∧ slots.length = rowCount ∧ (field.layout = .required → none ∉ slots) :=
  Proofs.Formats.Parquet.DictionaryChunk.scanColumn_ordered decoded

end Silmaril.Formats.Parquet.DictionaryChunk
