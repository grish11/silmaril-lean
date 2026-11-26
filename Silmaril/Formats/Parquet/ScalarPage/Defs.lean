module

public import Silmaril.Formats.Parquet.FlatPage.Defs
public import Silmaril.Formats.Parquet.Payload.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.Defs

/-! A checked adapter from explicit Parquet data-page parameters and an exact
body slice to a typed list of nullable scalar slots. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ScalarPage

structure Sizes where
  compressed : Nat
  uncompressed : Nat
  deriving DecidableEq, Repr

structure Limits where
  compressedBytes : Nat
  uncompressedBytes : Nat
  levels : Hybrid.Limits
  gzipCalls : Nat
  deriving DecidableEq, Repr

/-- Header-independent inputs. Natural numbers stand for nonnegative Thrift
counts and lengths. Missing V2 compression flags take the wire default. -/
inductive Version where
  | v1 (definitionEncoding repetitionEncoding : Int)
  | v2 (nulls rows repetitionBytes definitionBytes : Nat) (isCompressed : Option Bool)
  deriving DecidableEq, Repr

structure Parameters where
  sizes : Sizes
  schema : FlatPage.LevelSchema
  numValues : Nat
  codec : Int
  encoding : Int
  version : Version
  deriving DecidableEq, Repr

/-- Physical values supported by the existing PLAIN codec. -/
inductive Kind where
  | int32 | int64 | boolean | floatBits | doubleBits | fixedLenBytes (width : Nat)
  | byteArray (limits : Plain.ByteArray.Limits)
  deriving DecidableEq, Repr

abbrev Kind.Value : Kind → Type
  | .int32 => Int32
  | .int64 => Int64
  | .boolean => Bool
  | .floatBits => UInt32
  | .doubleBits => UInt64
  | .fixedLenBytes _ => Bytes
  | .byteArray _ => Bytes

def Kind.readPlain : (kind : Kind) → Nat → Bytes → Except Plain.Error (List kind.Value)
  | .int32 => Plain.decodeInt32
  | .int64 => Plain.decodeInt64
  | .boolean => Plain.decodeBoolean
  | .floatBits => Plain.decodeFloatBits
  | .doubleBits => Plain.decodeDoubleBits
  | .fixedLenBytes width => Plain.decodeFixedLenBytes width
  | .byteArray limits => Plain.ByteArray.decode limits

inductive Error where
  | unsupportedEncoding (id : Int)
  | unsupportedLevelEncoding
  | invalidPageSize
  | invalidNullCount
  | invalidRowCount
  | invalidLevelExtent
  | levels (error : FlatPage.Error)
  | payload (error : Payload.Error)
  | plain (error : Plain.Error)
  deriving DecidableEq, Repr

structure Prepared where
  mask : List Bool
  scalars : Bytes
  deriving DecidableEq

def Limits.payloadBounds (limits : Limits) (sizes : Sizes) (levelBytes : Nat) : Payload.Bounds :=
  ⟨sizes.compressed - levelBytes, limits.compressedBytes,
    sizes.uncompressed - levelBytes, limits.uncompressedBytes, limits.gzipCalls⟩

def v2Codec (columnCodec : Int) (isCompressed : Option Bool) : Int :=
  if isCompressed.getD true then columnCodec else Payload.Codec.uncompressed.id

/-- Validate the exact input extent and page-wide caps before making slices
or expanding a payload. The Thrift header stores page sizes as signed i32. -/
def validate (params : Parameters) (limits : Limits) (source : Bytes) :
    Except Error FlatPage.Layout :=
  let sizeLimit : Nat := 2 ^ 31
  if params.encoding ≠ 0 then .error (.unsupportedEncoding params.encoding)
  else if sizeLimit ≤ params.sizes.compressed ∨ sizeLimit ≤ params.sizes.uncompressed then
    .error .invalidPageSize
  else if limits.compressedBytes < params.sizes.compressed then .error (.payload .compressedLimit)
  else if limits.uncompressedBytes < params.sizes.uncompressed then .error (.payload .outputLimit)
  else if source.length ≠ params.sizes.compressed then .error (.payload .compressedSizeMismatch)
  else if Hybrid.runLimit ≤ params.numValues ∨ limits.levels.values < params.numValues then
    .error (.levels .countLimit)
  else
    match params.schema.layout? with
    | some layout => .ok layout
    | none => .error (.levels .unsupportedLevels)

/-- V2 leaves the level prefix uncompressed. Its extent must fit both sizes
before either size is reduced to describe the scalar suffix. -/
def splitV2 (sizes : Sizes) (byteLimit repetitionBytes definitionBytes : Nat)
    (source : Bytes) : Except Error (Bytes × List UInt8) :=
  if repetitionBytes ≠ 0 then .error (.levels .unexpectedRepetitionSection)
  else if sizes.compressed < definitionBytes ∨ sizes.uncompressed < definitionBytes then
    .error .invalidLevelExtent
  else if source.length ≠ sizes.compressed then .error (.payload .compressedSizeMismatch)
  else if byteLimit < definitionBytes then .error (.levels .definitionByteLimit)
  else
    let bytes := source.toList
    .ok (Bytes.ofList (bytes.take definitionBytes), bytes.drop definitionBytes)

def prepareV1 (params : Parameters) (limits : Limits) (layout : FlatPage.Layout)
    (definitionEncoding repetitionEncoding : Int) (source : Bytes) : Except Error Prepared := do
  if definitionEncoding ≠ 3 ∨ repetitionEncoding ≠ 3 then throw .unsupportedLevelEncoding
  else
    let body ← (Payload.decode (limits.payloadBounds params.sizes 0)
      params.codec source.toList).mapError Error.payload
    let sections ← (FlatPage.split layout limits.levels.bytes (.v1 (Bytes.ofList body))).mapError
      Error.levels
    let mask ← (FlatPage.readMask layout params.numValues limits.levels sections.definitions).mapError
      Error.levels
    pure ⟨mask, sections.scalars⟩

def prepareV2 (params : Parameters) (limits : Limits) (layout : FlatPage.Layout)
    (nulls rows repetitionBytes definitionBytes : Nat) (isCompressed : Option Bool)
    (source : Bytes) : Except Error Prepared := do
  if params.numValues < nulls then throw .invalidNullCount
  else if rows ≠ params.numValues then throw .invalidRowCount
  else
    let (definitions, encoded) ← splitV2 params.sizes limits.levels.bytes repetitionBytes
      definitionBytes source
    let mask ← (FlatPage.readMask layout params.numValues limits.levels definitions).mapError
      Error.levels
    if mask.count true ≠ params.numValues - nulls then throw (.levels .presentCountMismatch)
    else
      let scalars ← (Payload.decode (limits.payloadBounds params.sizes definitionBytes)
        (v2Codec params.codec isCompressed) encoded).mapError Error.payload
      pure ⟨mask, Bytes.ofList scalars⟩

/-- Establish a checked mask and the exact decompressed scalar slice. -/
def prepare (params : Parameters) (limits : Limits) (source : Bytes) : Except Error Prepared := do
  let layout ← validate params limits source
  match params.version with
  | .v1 definitionEncoding repetitionEncoding =>
    prepareV1 params limits layout definitionEncoding repetitionEncoding source
  | .v2 nulls rows repetitionBytes definitionBytes isCompressed =>
    prepareV2 params limits layout nulls rows repetitionBytes definitionBytes isCompressed source

/-- For V1 the scalar count comes from the mask. For V2 preparation has
already checked that the mask count equals the header's present count. -/
def decode (kind : Kind) (params : Parameters) (limits : Limits) (source : Bytes) :
    Except Error (List (Option kind.Value)) := do
  let page ← prepare params limits source
  let values ← (kind.readPlain (page.mask.count true) page.scalars).mapError Error.plain
  (FlatPage.reconstruct page.mask values).mapError Error.levels

/-- The selected payload relation and both exact byte counts. -/
def ExactPayload (compressed uncompressed : Nat) (codecId : Int)
    (input output : List UInt8) : Prop :=
  input.length = compressed ∧ output.length = uncompressed ∧
    ∃ codec, Payload.Codec.ofId codecId = some codec ∧
      Payload.Decodes uncompressed codec input output

/-- Successful preparation retains the exact V1 or V2 wire decomposition. -/
def PreparedWire (params : Parameters) (limits : Limits) (layout : FlatPage.Layout)
    (source : Bytes) (page : Prepared) : Prop :=
  match params.version with
  | .v1 definitionEncoding repetitionEncoding =>
    definitionEncoding = 3 ∧ repetitionEncoding = 3 ∧
      ∃ body sections, ExactPayload params.sizes.compressed params.sizes.uncompressed
          params.codec source.toList body ∧
        FlatPage.split layout limits.levels.bytes (.v1 (Bytes.ofList body)) = .ok sections ∧
        FlatPage.readMask layout params.numValues limits.levels sections.definitions =
          .ok page.mask ∧ page.scalars = sections.scalars
  | .v2 nulls rows repetitionBytes definitionBytes isCompressed =>
    nulls ≤ params.numValues ∧ rows = params.numValues ∧ repetitionBytes = 0 ∧
      definitionBytes ≤ params.sizes.compressed ∧ definitionBytes ≤ params.sizes.uncompressed ∧
      definitionBytes ≤ limits.levels.bytes ∧
      ∃ definitions : Bytes, ∃ encoded : List UInt8,
        definitions.length = definitionBytes ∧ source.toList = definitions.toList ++ encoded ∧
        FlatPage.readMask layout params.numValues limits.levels definitions = .ok page.mask ∧
        page.mask.count true = params.numValues - nulls ∧
        ExactPayload (params.sizes.compressed - definitionBytes)
          (params.sizes.uncompressed - definitionBytes) (v2Codec params.codec isCompressed)
          encoded page.scalars.toList

/-- Fixed-width sizes depend on the expected count. BYTE_ARRAY sizes also
include the four-octet length and actual payload of each returned value. -/
def Kind.plainByteCount : (kind : Kind) → Nat → List kind.Value → Nat
  | .int32, count, _ | .floatBits, count, _ => count * 4
  | .int64, count, _ | .doubleBits, count, _ => count * 8
  | .boolean, count, _ => Plain.booleanByteCount count
  | .fixedLenBytes width, count, _ => count * width
  | .byteArray _, _, values => Plain.ByteArray.encodedSize values

end Silmaril.Formats.Parquet.ScalarPage
