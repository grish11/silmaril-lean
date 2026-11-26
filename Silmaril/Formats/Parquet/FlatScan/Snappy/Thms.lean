module

public import Silmaril.Formats.Parquet.FlatScan.Snappy.Defs
import Silmaril.Proofs.Formats.Parquet.FlatScan.Snappy.Correctness

/-! Exact codec-covered extents and ordered nullable observations. -/

public section

namespace Silmaril.Formats.Parquet.FlatScan.Snappy

/-- A successful column scan admits codec 1 and frames the matched chunk
from the original source. -/
theorem scanColumn_framed {ε : Type} {limits : Limits} {decoder : DecodePage ε} {source : Bytes}
    {footerStart rows : Nat} {field : Field} {column : Footer.ColumnChunk} {result : ColumnValues rows}
    (scanned : scanColumnSnappy limits decoder source footerStart field rows column = .ok result) :
    column.metadata.codec = 1 ∧ ∃ span frames,
      Page.columnSpan footerStart column.metadata = some span ∧
      Page.readChunk limits.page source span = .ok frames :=
  Proofs.Formats.Parquet.FlatScan.Snappy.scanColumn_framed scanned

/-- The decoder retains the original header parameters and accounts for the
exact framed input and slots under the checked Snappy column codec. -/
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
      | .v2 nulls _ _ _ _ => (slots.filterMap id).length = params.numValues - nulls :=
  Proofs.Formats.Parquet.FlatScan.Snappy.decodeFrame_wire decoded

end Silmaril.Formats.Parquet.FlatScan.Snappy
