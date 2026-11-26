module

public import Silmaril.Formats.Parquet.FlatScan.Scalar.Defs
public import Silmaril.Formats.Parquet.DeltaPage.Defs

/-! Dispatch flat INT32 data pages by their checked V1 or V2 value encoding. -/

public section

namespace Silmaril.Formats.Parquet.FlatScan.Delta

inductive Error where
  | unsupportedKind
  | unsupportedEncoding (encoding : Int)
  | plain (reason : ScalarPage.Error)
  | delta (reason : DeltaPage.Error)
  deriving DecidableEq, Repr

/-- Decode the exact on-disk body after column and frame admission. The raw
encoding in the page header selects the decoder. -/
def decodePage (limits : DeltaPage.Limits) : DecodePage Error := fun field header body =>
  match int32PageParameters field header with
  | none => .error .unsupportedKind
  | some params =>
    if params.encoding = 0 then
      (ScalarPage.decode .int32 params limits.page body).mapError .plain
    else if params.encoding = 5 then
      (DeltaPage.decode (.signed .int32) params limits body).mapError .delta
    else
      .error (.unsupportedEncoding params.encoding)

end Silmaril.Formats.Parquet.FlatScan.Delta
