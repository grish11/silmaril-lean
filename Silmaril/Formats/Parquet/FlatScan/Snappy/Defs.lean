module

public import Silmaril.Formats.Parquet.FlatScan.Scalar.Defs

/-! Checked PLAIN INT32 decoding for the exact body of a page in a Snappy column. -/

public section

namespace Silmaril.Formats.Parquet.FlatScan.Snappy

/-- Callback for `scanColumnSnappy`. The scan checks the footer codec and
body extent. ScalarPage applies Snappy to the full V1 body or the V2 value
suffix selected by the resolved header flag. -/
def decodePage (limits : ScalarPage.Limits) : DecodePage AdapterError := fun field header body =>
  match int32PageParameters field header with
  | none => .error .unsupportedKind
  | some params =>
    (ScalarPage.decode .int32 {params with codec := Payload.Codec.snappy.id} limits body).mapError .scalar

end Silmaril.Formats.Parquet.FlatScan.Snappy
