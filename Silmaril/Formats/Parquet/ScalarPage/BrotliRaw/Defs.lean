module

public import Silmaril.Formats.Parquet.ScalarPage.Defs
public import Silmaril.Formats.Compression.Brotli.Defs

/-! # Opt-in Parquet codec 4 with raw Brotli meta-blocks

Expand the exact body of a flat PLAIN data page. V1 covers the entire
body. V2 preserves the original level bytes and selects compression
only for the value suffix. The decoder takes externally framed bytes
and parameters, leaving page CRC validation to the framing layer.
-/

@[expose] public section

namespace Silmaril.Formats.Parquet.ScalarPage.BrotliRaw

open Silmaril.Formats.Compression

structure Limits where
  window : Nat
  steps : Nat
  deriving DecidableEq, Repr

inductive Error where
  | codec (actual : Int)
  | page (reason : ScalarPage.Error)
  | stream (reason : Brotli.Error)
  deriving DecidableEq, Repr

def streamLimits (limits : Limits) (bounds : Payload.Bounds) : Brotli.Limits :=
  ⟨bounds.compressedSize, bounds.expectedSize, limits.window, limits.steps⟩

/-- The stream's output budget is the declared size. Exceeding that size
is a mismatch, while exceeding the caller cap is checked before decoding. -/
def streamError : Brotli.Error → Error
  | .outputLimit => .page (.payload .outputSizeMismatch)
  | error => .stream error

/-- Expand an exact compression slice using only the raw-meta-block profile. -/
def decodePayload (limits : Limits) (bounds : Payload.Bounds) (input : List UInt8) :
    Except Error (List UInt8) :=
  if bounds.compressedLimit < bounds.compressedSize then .error (.page (.payload .compressedLimit))
  else if bounds.outputLimit < bounds.expectedSize then .error (.page (.payload .outputLimit))
  else if !Payload.Internal.hasLength bounds.compressedSize input then
    .error (.page (.payload .compressedSizeMismatch))
  else do
    let out ← (Brotli.decode (streamLimits limits bounds) input).mapError streamError
    if out.length = bounds.expectedSize then pure out else .error (.page (.payload .outputSizeMismatch))

/-- Expand a codec-4 body before interpreting its levels and PLAIN values. -/
def decodePage (limits : Limits) (pageLimits : ScalarPage.Limits) (params : ScalarPage.Parameters)
    (source : Bytes) : Except Error (List UInt8) :=
  if params.codec ≠ Payload.Codec.brotli.id then .error (.codec params.codec)
  else do
    let _ ← (ScalarPage.validate params pageLimits source).mapError Error.page
    match params.version with
    | .v1 _ _ =>
      decodePayload limits (pageLimits.payloadBounds params.sizes 0) source.toList
    | .v2 _ _ repetitionBytes definitionBytes flag =>
      let (levels, encoded) ←
        (ScalarPage.splitV2 params.sizes pageLimits.levels.bytes repetitionBytes definitionBytes source)
          |>.mapError Error.page
      let bounds := pageLimits.payloadBounds params.sizes definitionBytes
      let raw := Payload.Codec.uncompressed.id
      let action := if ScalarPage.v2Codec params.codec flag = raw then
        (Payload.decode bounds raw encoded).mapError (.page ∘ .payload)
      else
        decodePayload limits bounds encoded
      let plain ← action
      pure (levels.toList ++ plain)

/-- Accepted streams satisfy the RFC raw wire relation and both codec limits. -/
def StreamWire (limits : Limits) (input output : List UInt8) : Prop :=
  ∃ wbits steps, Brotli.StreamWire input output wbits steps ∧
    Brotli.windowSize wbits ≤ limits.window ∧ steps ≤ limits.steps

def PayloadWire (limits : Limits) (bounds : Payload.Bounds) (input output : List UInt8) : Prop :=
  input.length = bounds.compressedSize ∧ input.length ≤ bounds.compressedLimit ∧
  output.length = bounds.expectedSize ∧ output.length ≤ bounds.outputLimit ∧
  StreamWire limits input output

/-- The original and expanded bodies have exact page-wide extents. V2
retains the same original level prefix and changes only the value suffix. -/
def PageWire (limits : Limits) (pageLimits : ScalarPage.Limits) (params : ScalarPage.Parameters)
    (source : Bytes) (output : List UInt8) : Prop :=
  params.codec = Payload.Codec.brotli.id ∧
  source.length = params.sizes.compressed ∧ source.length ≤ pageLimits.compressedBytes ∧
  output.length = params.sizes.uncompressed ∧ output.length ≤ pageLimits.uncompressedBytes ∧
  match params.version with
  | .v1 _ _ => StreamWire limits source.toList output
  | .v2 _ _ repetitionBytes definitionBytes flag =>
    repetitionBytes = 0 ∧ definitionBytes ≤ params.sizes.compressed ∧
    definitionBytes ≤ params.sizes.uncompressed ∧ definitionBytes ≤ pageLimits.levels.bytes ∧
    ∃ levels encoded plain : List UInt8,
      levels.length = definitionBytes ∧ source.toList = levels ++ encoded ∧ output = levels ++ plain ∧
      encoded.length = params.sizes.compressed - definitionBytes ∧
      plain.length = params.sizes.uncompressed - definitionBytes ∧
      if flag.getD true then StreamWire limits encoded plain else plain = encoded

end Silmaril.Formats.Parquet.ScalarPage.BrotliRaw
