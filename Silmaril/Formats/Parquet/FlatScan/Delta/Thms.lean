module

public import Silmaril.Formats.Parquet.FlatScan.Delta.Defs
import Silmaril.Proofs.Formats.Parquet.FlatScan.Delta.Correctness

/-! Exact frame-body dispatch and slot counts for the two INT32 encodings. -/

public section

namespace Silmaril.Formats.Parquet.FlatScan.Delta

/-- Success returns exactly the ordered slots of the decoder selected by the
original header, on the original framed payload. -/
theorem decodeFrame_ok_iff {limits : DeltaPage.Limits} {source : Bytes} {field : Field}
    {frame : Page.Frame} {slots : List (Option Int32)} :
    let body := Footer.fileBytes source frame.payload.start frame.payload.stop
    decodePage limits field frame.value body = .ok slots ↔
      ∃ params, int32PageParameters field frame.value = some params ∧
        ((params.encoding = 0 ∧ ScalarPage.decode .int32 params limits.page body = .ok slots) ∨
         (params.encoding = 5 ∧ DeltaPage.decode (.signed .int32) params limits body = .ok slots)) :=
  Proofs.Formats.Parquet.FlatScan.Delta.decodeFrame_ok_iff

theorem decodeFrame_counts {limits : DeltaPage.Limits} {source : Bytes} {field : Field}
    {frame : Page.Frame} {slots : List (Option Int32)} {params : ScalarPage.Parameters}
    (selected : int32PageParameters field frame.value = some params)
    (decoded : decodePage limits field frame.value
      (Footer.fileBytes source frame.payload.start frame.payload.stop) = .ok slots) :
    slots.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (slots.filterMap id).length = params.numValues - nulls :=
  Proofs.Formats.Parquet.FlatScan.Delta.decodeFrame_counts selected decoded

end Silmaril.Formats.Parquet.FlatScan.Delta
