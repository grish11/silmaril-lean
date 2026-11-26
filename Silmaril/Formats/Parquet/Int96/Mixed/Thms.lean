module

public import Silmaril.Formats.Parquet.Int96.Mixed.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Int96.Mixed.Wire

public section

namespace Silmaril.Formats.Parquet.Int96.Mixed

/-- Planning retains the original frame, page ordinal and header parameters.
The admitted encoding is exactly the declared tag. -/
theorem planData_sound {leaf : Footer.SchemaElement} {frame : Parquet.Page.Frame}
    {ordinal : Nat} {page : DataPage} (h : planData leaf frame ordinal = .ok page) :
    page.frame = frame ∧ page.ordinal = ordinal ∧
      Int96.Page.parameters leaf 0 frame.value = .ok page.params ∧
      page.params.encoding = (match page.encoding with | .plain => 0 | .dictionary => 8) :=
  Proofs.Formats.Parquet.Int96.Mixed.planData_sound h

/-- A planned page uses its original header and body in the selected decoder.
Each branch forwards its typed failure at the original frame coordinates. -/
theorem decodePage_dispatch (limits : Dictionary.Limits) (policy : Policy) (source : Bytes)
    (leaf : Footer.SchemaElement) (dictionary : Array (Int96.Page.Value policy))
    {frame : Parquet.Page.Frame} {ordinal : Nat} {page : DataPage}
    (planned : planData leaf frame ordinal = .ok page) :
    decodePage limits policy source leaf dictionary page =
      if page.params.encoding = 0 then
        (Int96.Page.decode policy leaf 0 frame.value limits.scalar (Dictionary.frameBody source frame)).mapError
          (.page ordinal frame.header.start ∘ .plain)
      else
        (Dictionary.decodeData limits dictionary page.params (Dictionary.frameBody source frame)).mapError
          (.page ordinal frame.header.start ∘ .dictionary) :=
  Proofs.Formats.Parquet.Int96.Mixed.decodePage_dispatch limits policy source leaf dictionary planned

/-- Both branches return the exact logical slot count and the result of the
decoder selected by the original header. -/
theorem decodePage_wire {limits : Dictionary.Limits} {policy : Policy} {source : Bytes}
    {leaf : Footer.SchemaElement} {dictionary : Array (Int96.Page.Value policy)}
    {frame : Parquet.Page.Frame} {ordinal : Nat} {page : DataPage} {slots : Dictionary.Slots policy}
    (planned : planData leaf frame ordinal = .ok page)
    (decoded : decodePage limits policy source leaf dictionary page = .ok slots) :
    DataWire limits source leaf dictionary frame slots ∧ slots.length = page.params.numValues :=
  Proofs.Formats.Parquet.Int96.Mixed.decodePage_wire planned decoded

/-- Exactly one leading PLAIN dictionary frame precedes the original ordered
data frames. Their own header tags select the decoders, and the flattened
slots match the checked row count. -/
theorem read_wire {limits : Dictionary.Limits} {policy : Policy} {source : Bytes}
    {footerStart rowCount : Nat} {leaf : Footer.SchemaElement} {column : Footer.ColumnMetadata}
    {slots : Dictionary.Slots policy}
    (h : Mixed.read limits policy source footerStart rowCount leaf column = .ok slots) :
    ∃ span first rest header dictionary pages,
      Parquet.Page.columnSpan footerStart column = some span ∧
      Parquet.Page.readChunk limits.framing source span = .ok (first :: rest) ∧
      span.stop ≤ source.length ∧
      Parquet.Page.Chain span span.start span.stop (first :: rest) ∧
      column.dictionaryPageOffset = some (first.header.start : Int) ∧
      rest.head?.map (fun frame => (frame.header.start : Int)) = some column.dataPageOffset ∧
      first.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      Dictionary.readDictionary limits policy source first = .ok dictionary ∧
      List.Forall₂ (DataWire limits source leaf dictionary) rest pages ∧
      slots = pages.flatten ∧ slots.length = rowCount :=
  Proofs.Formats.Parquet.Int96.Mixed.read_wire h

end Silmaril.Formats.Parquet.Int96.Mixed
