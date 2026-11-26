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

/-- Translate an original header and matched flat leaf for an uncompressed
column. Preserve the raw scalar and level encodings and the declared V2 flag. -/
def int32PageParameters (field : Field) (header : Page.Header) : Option ScalarPage.Parameters :=
  let params := fun count encoding version =>
    ⟨⟨header.compressedSize, header.uncompressedSize⟩,
      ⟨0, if field.layout == .required then 0 else 1⟩, count, 0, encoding, version⟩
  match header.kind with
  | .dataV1 h => some (params h.numValues h.encoding (.v1 h.definitionLevelEncoding h.repetitionLevelEncoding))
  | .dataV2 h => some (params h.numValues h.encoding
      (.v2 h.numNulls h.numRows h.repetitionBytes h.definitionBytes (some h.isCompressed)))
  | .dictionary _ | .skipped _ => none

/-- Callback for `scanFileRowGroup` and `scanRowGroup`. The scan checks the
on-disk extent and rejects compressed, non-PLAIN and CRC-bearing inputs. -/
def decodeInt32Page (limits : ScalarPage.Limits) : DecodePage AdapterError := fun field header body => do
  let some params := int32PageParameters field header | throw .unsupportedKind
  (ScalarPage.decode .int32 params limits body).mapError .scalar

/-- The flat V1 callback uses the exact sizes and encodings from its header. -/
theorem decodeInt32Page_v1 (limits : ScalarPage.Limits) (field : Field)
    (compressed uncompressed : Nat) (crc : Option UInt32) (info : Page.DataV1) (body : Bytes) :
    decodeInt32Page limits field ⟨uncompressed, compressed, crc, .dataV1 info⟩ body =
      (ScalarPage.decode .int32
        ⟨⟨compressed, uncompressed⟩, ⟨0, if field.layout == .required then 0 else 1⟩,
          info.numValues, 0, info.encoding, .v1 info.definitionLevelEncoding info.repetitionLevelEncoding⟩
        limits body).mapError AdapterError.scalar := by
  rfl

end Silmaril.Formats.Parquet.FlatScan
