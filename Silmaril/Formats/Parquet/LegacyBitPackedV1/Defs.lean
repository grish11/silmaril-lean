module

public import Silmaril.Formats.Parquet.Page.Header.Defs
public import Silmaril.Formats.Parquet.ScalarPage.Defs
public import Silmaril.Formats.Parquet.Footer.Metadata.Defs
public import Silmaril.Formats.Parquet.BitPackedLevels.Defs

/-! Opt-in, uncompressed V1 PLAIN INT32 pages with legacy definition levels. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.LegacyBitPackedV1

inductive Error where
  | unsupportedSchema
  | unsupportedCodec (id : Int)
  | crcUnsupported
  | unsupportedPage
  | page (error : ScalarPage.Error)
  | payload (error : Payload.Error)
  | levels (error : BitPackedLevels.Error)
  | plain (error : Plain.Error)
  | slots (error : FlatPage.Error)
  deriving DecidableEq, Repr

structure Profile (physical : Footer.PhysicalType) (schema : FlatPage.LevelSchema) (codec : Int)
    (header : Page.Header) (info : Page.DataV1) : Prop where
  int32 : physical = .int32
  optional : schema = ⟨0, 1⟩
  uncompressed : codec = 0
  crcAbsent : header.crc = none
  v1 : header.kind = .dataV1 info
  plain : info.encoding = 0
  definitions : info.definitionLevelEncoding = 4
  repetitions : info.repetitionLevelEncoding = 3

/-- The header retains the original tags. The zero-width repetition section
is absent under this profile's flat schema. -/
def admit (physical : Footer.PhysicalType) (schema : FlatPage.LevelSchema)
    (codec : Int) (header : Page.Header) : Except Error Page.DataV1 :=
  if physical ≠ .int32 ∨ schema.maxRepetition ≠ 0 ∨ schema.maxDefinition ≠ 1 then
    .error .unsupportedSchema
  else if codec ≠ 0 then .error (.unsupportedCodec codec)
  else if header.crc ≠ none then .error .crcUnsupported
  else
    match header.kind with
    | .dataV1 info =>
      if info.encoding ≠ 0 then .error (.page (.unsupportedEncoding info.encoding))
      else if info.definitionLevelEncoding ≠ 4 ∨ info.repetitionLevelEncoding ≠ 3 then
        .error (.page .unsupportedLevelEncoding)
      else .ok info
    | _ => .error .unsupportedPage

structure Prepared where
  levels : List Nat
  values : Bytes
  deriving DecidableEq

def Prepared.mask (page : Prepared) : List Bool :=
  page.levels.map (· == 1)

structure PreparedWire (header : Page.Header) (info : Page.DataV1) (limits : ScalarPage.Limits)
    (body : Bytes) (page : Prepared) : Prop where
  compressed : body.length = header.compressedSize
  uncompressed : body.length = header.uncompressedSize
  storedCap : body.length ≤ limits.compressedBytes
  outputCap : body.length ≤ limits.uncompressedBytes
  slotCap : info.numValues ≤ limits.levels.values
  sections : ∃ definitions : Bytes, definitions.length ≤ limits.levels.bytes ∧
    body = definitions.append page.values ∧ BitPackedLevels.Wire 1 info.numValues definitions page.levels

/-- Frame association, column identity, and schema levels come from the caller.
This adapter checks the supplied physical profile and the exact body bounds. -/
def prepare (physical : Footer.PhysicalType) (schema : FlatPage.LevelSchema) (codec : Int)
    (header : Page.Header) (limits : ScalarPage.Limits) (body : Bytes) : Except Error Prepared := do
  let info ← admit physical schema codec header
  let params : ScalarPage.Parameters :=
    ⟨⟨header.compressedSize, header.uncompressedSize⟩, schema, info.numValues, codec, info.encoding,
      .v1 info.definitionLevelEncoding info.repetitionLevelEncoding⟩
  let _ ← (ScalarPage.validateFor 0 params limits body).mapError Error.page
  let raw ← (Payload.decode (limits.payloadBounds params.sizes 0) codec body.toList).mapError Error.payload
  let (levels, values) ← (BitPackedLevels.readPrefix 1 info.numValues
    ⟨limits.levels.values, limits.levels.bytes⟩ (Bytes.ofList raw)).mapError Error.levels
  pure ⟨levels, values⟩

structure Decoded where
  slots : List (Option Int32)
  nullCount : Nat
  deriving DecidableEq, Repr

/-- Read the exact value suffix at the present count from the definition mask. -/
def decodeInt32 (physical : Footer.PhysicalType) (schema : FlatPage.LevelSchema) (codec : Int)
    (header : Page.Header) (limits : ScalarPage.Limits) (body : Bytes) : Except Error Decoded := do
  let page ← prepare physical schema codec header limits body
  let mask := page.mask
  let values ← (Plain.decodeInt32 (mask.count true) page.values).mapError Error.plain
  let slots ← (FlatPage.reconstruct mask values).mapError Error.slots
  pure ⟨slots, mask.count false⟩

end Silmaril.Formats.Parquet.LegacyBitPackedV1
