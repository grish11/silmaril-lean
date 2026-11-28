module

public import Silmaril.Formats.Parquet.FlatScan.Delta.Defs
import all Silmaril.Formats.Parquet.FlatScan.Delta.Defs
import Silmaril.Formats.Parquet.DeltaPage.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatScan.Delta

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.FlatScan
open Silmaril.Formats.Parquet.FlatScan.Delta

theorem decodeFrame_ok_iff {limits : DeltaPage.Limits} {source : Bytes} {field : Field}
    {frame : Page.Frame} {slots : List (Option Int32)} :
    let body := Footer.fileBytes source frame.payload.start frame.payload.stop
    decodePage limits field frame.value body = .ok slots ↔
      ∃ params, int32PageParameters field frame.value = some params ∧
        ((params.encoding = 0 ∧ ScalarPage.decode .int32 params limits.page body = .ok slots) ∨
         (params.encoding = 5 ∧ DeltaPage.decode (.signed .int32) params limits body = .ok slots)) := by
  dsimp only
  cases params : int32PageParameters field frame.value with
  | none => simp [decodePage, params]
  | some info =>
    by_cases plain : info.encoding = 0
    · cases read : ScalarPage.decode .int32 info limits.page
          (Footer.fileBytes source frame.payload.start frame.payload.stop) <;>
        simp [decodePage, params, plain, read, Except.mapError]
    · by_cases delta : info.encoding = 5
      · cases read : DeltaPage.decode (.signed .int32) info limits
            (Footer.fileBytes source frame.payload.start frame.payload.stop) <;>
          simp [decodePage, params, delta, read, Except.mapError]
      · simp [decodePage, params, plain, delta]

theorem decodeFrame_counts {limits : DeltaPage.Limits} {source : Bytes} {field : Field}
    {frame : Page.Frame} {slots : List (Option Int32)} {params : ScalarPage.Parameters}
    (selected : int32PageParameters field frame.value = some params)
    (decoded : decodePage limits field frame.value
      (Footer.fileBytes source frame.payload.start frame.payload.stop) = .ok slots) :
    slots.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (slots.filterMap id).length = params.numValues - nulls := by
  obtain ⟨actual, eqParams, branch⟩ := decodeFrame_ok_iff.mp decoded
  rw [selected] at eqParams
  cases eqParams
  obtain ⟨_, plain⟩ | ⟨_, delta⟩ := branch
  · exact ScalarPage.decode_counts plain
  · exact DeltaPage.decode_counts delta

end Silmaril.Proofs.Formats.Parquet.FlatScan.Delta
