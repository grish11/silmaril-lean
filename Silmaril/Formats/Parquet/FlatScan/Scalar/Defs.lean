module

public import Silmaril.Formats.Parquet.FlatScan.Defs
public import Silmaril.Formats.Parquet.ScalarPage.Defs

/-! Instantiate the flat uncompressed INT32 scan's callback with the checked
scalar page decoder. -/

public section

namespace Silmaril.Formats.Parquet.FlatScan

inductive AdapterError where
  | unsupportedKind
  | scalar (error : ScalarPage.Error)
  deriving DecidableEq, Repr

/-- Callback for `scanFileRowGroup` and `scanRowGroup`. The scan checks the
on-disk extent and rejects compressed, non-PLAIN and CRC-bearing inputs. -/
def decodeInt32Page (limits : ScalarPage.Limits) : DecodePage AdapterError := fun field header body => do
  let (values, encoding, version) ← pageParameters header.kind
  let params : ScalarPage.Parameters := {
    sizes := ⟨header.compressedSize, header.uncompressedSize⟩
    schema := ⟨0, if field.layout == .required then 0 else 1⟩
    numValues := values
    codec := 0
    encoding := encoding
    version := version }
  (ScalarPage.decode .int32 params limits body).mapError .scalar
where
  pageParameters : Page.Kind → Except AdapterError (Nat × Int × ScalarPage.Version)
    | .dataV1 v1 =>
      .ok (v1.numValues, v1.encoding, .v1 v1.definitionLevelEncoding v1.repetitionLevelEncoding)
    | .dataV2 v2 =>
      .ok (v2.numValues, v2.encoding,
        .v2 v2.numNulls v2.numRows v2.repetitionBytes v2.definitionBytes (some v2.isCompressed))
    | .dictionary _ | .skipped _ => .error .unsupportedKind

end Silmaril.Formats.Parquet.FlatScan
