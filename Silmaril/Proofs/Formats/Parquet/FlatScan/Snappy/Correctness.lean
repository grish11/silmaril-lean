module

public import Silmaril.Formats.Parquet.FlatScan.Snappy.Defs
import all Silmaril.Formats.Parquet.FlatScan.Defs
import all Silmaril.Formats.Parquet.FlatScan.Snappy.Defs
import Silmaril.Formats.Parquet.ScalarPage.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatScan.Snappy

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.FlatScan
open Silmaril.Formats.Parquet.FlatScan.Snappy

theorem scanColumn_framed {ε : Type} {limits : Limits} {decoder : DecodePage ε} {source : Bytes}
    {footerStart rows : Nat} {field : Field} {column : Footer.ColumnChunk} {result : ColumnValues rows}
    (scanned : scanColumnSnappy limits decoder source footerStart field rows column = .ok result) :
    column.metadata.codec = 1 ∧ ∃ span frames,
      Page.columnSpan footerStart column.metadata = some span ∧
      Page.readChunk limits.page source span = .ok frames := by
  cases parsed : frameColumn (ε := ε) none false 1 limits source footerStart field rows column with
  | error reason =>
    simp [scanColumnSnappy, scanColumnCore, parsed, Bind.bind, Except.bind, Except.mapError] at scanned
  | ok frames =>
    simp only [frameColumn] at parsed
    split at parsed <;> try contradiction
    split at parsed <;> try contradiction
    split at parsed <;> try contradiction
    split at parsed <;> try contradiction
    split at parsed <;> try contradiction
    rename_i codec
    have admitted : column.metadata.codec = 1 := by simpa using codec
    split at parsed <;> try contradiction
    split at parsed <;> try contradiction
    split at parsed <;> try contradiction
    rename_i span located
    cases read : Page.readChunk limits.page source span with
    | error reason => simp [Except.mapError, read] at parsed
    | ok actual => exact ⟨admitted, span, actual, located, read⟩

theorem decodeFrame_wire {limits : ScalarPage.Limits} {source : Bytes} {field : Field}
    {frame : Page.Frame} {slots : List (Option Int32)}
    (decoded : decodePage limits field frame.value
      (Footer.fileBytes source frame.payload.start frame.payload.stop) = .ok slots) :
    let body := Footer.fileBytes source frame.payload.start frame.payload.stop
    ∃ base layout page values, int32PageParameters field frame.value = some base ∧
      let params := {base with codec := Payload.Codec.snappy.id}
      ScalarPage.validate params limits body = .ok layout ∧
      ScalarPage.PreparedWire params limits layout body page ∧
      ScalarPage.Kind.int32.readPlain (page.mask.count true) page.scalars = .ok values ∧
      slots.map Option.isSome = page.mask ∧ slots.filterMap id = values ∧
      slots.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (slots.filterMap id).length = params.numValues - nulls := by
  let body := Footer.fileBytes source frame.payload.start frame.payload.stop
  cases selected : int32PageParameters field frame.value with
  | none => simp [decodePage, selected] at decoded
  | some base =>
    let params := {base with codec := Payload.Codec.snappy.id}
    have mapped : (ScalarPage.decode .int32 params limits body).mapError AdapterError.scalar = .ok slots := by
      simpa [decodePage, selected, params, body] using decoded
    have run : ScalarPage.decode .int32 params limits body = .ok slots := by
      cases scalar : ScalarPage.decode .int32 params limits body <;>
        simp [scalar, Except.mapError] at mapped ⊢
      exact mapped
    obtain ⟨page, values, prepared, plain, mask, ordered, _, _⟩ := ScalarPage.decode_sound run
    obtain ⟨layout, valid, wire⟩ := ScalarPage.prepare_sound prepared
    obtain ⟨count, present⟩ := ScalarPage.decode_counts run
    exact ⟨base, layout, page, values, rfl, valid, wire, plain, mask, ordered, count, present⟩

end Silmaril.Proofs.Formats.Parquet.FlatScan.Snappy
