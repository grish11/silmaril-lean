module

public import Silmaril.Formats.Parquet.ScalarPage.BrotliRaw.Defs
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Silmaril.Formats.Parquet.Payload.Thms
import Silmaril.Formats.Compression.Brotli.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Parquet.ScalarPage.BrotliRaw

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.ScalarPage.BrotliRaw
open Silmaril.Formats.Compression

theorem decodePayload_sound {limits : Limits} {bounds : Payload.Bounds} {input output : List UInt8}
    (read : decodePayload limits bounds input = .ok output) : PayloadWire limits bounds input output := by
  unfold decodePayload at read
  split at read <;> try contradiction
  rename_i inputFits
  split at read <;> try contradiction
  rename_i outputFits
  split at read <;> try contradiction
  rename_i hasLength
  cases decode : Brotli.decode (streamLimits limits bounds) input with
  | error error => simp [decode, Except.mapError, bind, Except.bind] at read
  | ok decoded =>
    simp only [decode, Except.mapError, bind, Except.bind] at read
    split at read <;> try contradiction
    rename_i extent
    cases read
    obtain ⟨wbits, steps, wire, _, _, window, fuel⟩ := Brotli.decode_sound decode
    have inputSize : input.length = bounds.compressedSize :=
      Payload.hasLength_iff.mp (by simpa using hasLength)
    exact ⟨inputSize, by omega, extent, by omega, wbits, steps, wire, window, fuel⟩

theorem decodePayload_streamError {limits : Limits} {bounds : Payload.Bounds}
    {input : List UInt8} {error : Brotli.Error}
    (inputFits : bounds.compressedSize ≤ bounds.compressedLimit)
    (outputFits : bounds.expectedSize ≤ bounds.outputLimit) (extent : input.length = bounds.compressedSize)
    (read : Brotli.decode (streamLimits limits bounds) input = .error error) :
    decodePayload limits bounds input = .error (streamError error) := by
  simp [decodePayload, Nat.not_lt.mpr inputFits, Nat.not_lt.mpr outputFits,
    Payload.hasLength_iff.mpr extent, read, Except.mapError, bind, Except.bind]

private theorem validate_bounds {limits : ScalarPage.Limits} {params : ScalarPage.Parameters}
    {source : Bytes} {layout : FlatPage.Layout} (read : ScalarPage.validate params limits source = .ok layout) :
    source.length = params.sizes.compressed ∧ params.sizes.compressed ≤ limits.compressedBytes ∧
      params.sizes.uncompressed ≤ limits.uncompressedBytes := by
  simp only [ScalarPage.validate, ScalarPage.validateFor] at read
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  rename_i compressed
  split at read <;> try contradiction
  rename_i uncompressed
  split at read <;> try contradiction
  rename_i extent
  exact ⟨not_not.mp extent, by omega, by omega⟩

private theorem raw_sound {bounds : Payload.Bounds} {encoded plain : List UInt8}
    (read : Payload.decode bounds Payload.Codec.uncompressed.id encoded = .ok plain) :
    encoded.length = bounds.compressedSize ∧ plain.length = bounds.expectedSize ∧ plain = encoded := by
  obtain ⟨codec, id, wire, inputSize, _, outputSize, _⟩ := Payload.decode_sound read
  have raw : codec = .uncompressed := by simpa [Payload.Codec.ofId, Payload.Codec.id] using id.symm
  subst codec
  cases wire
  exact ⟨inputSize, outputSize, rfl⟩

private theorem append_ok {action : Except Error (List UInt8)} {levels output : List UInt8}
    (read : (do let plain ← action; pure (levels ++ plain)) = .ok output) :
    ∃ plain, action = .ok plain ∧ output = levels ++ plain := by
  cases action with
  | error _ => cases read
  | ok plain => cases read; exact ⟨plain, rfl, rfl⟩

theorem decodePage_sound {limits : Limits} {pageLimits : ScalarPage.Limits}
    {params : ScalarPage.Parameters} {source : Bytes} {output : List UInt8}
    (read : decodePage limits pageLimits params source = .ok output) :
    PageWire limits pageLimits params source output := by
  unfold decodePage at read
  by_cases codec : params.codec = Payload.Codec.brotli.id
  · cases validated : ScalarPage.validate params pageLimits source with
    | error _ => simp [codec, validated, Except.mapError, bind, Except.bind] at read
    | ok layout =>
      simp only [codec, ne_eq, not_true_eq_false, ↓reduceIte, validated, Except.mapError, bind, Except.bind] at read
      obtain ⟨extent, inputCap, outputCap⟩ := validate_bounds validated
      refine ⟨codec, extent, extent ▸ inputCap, ?_⟩
      cases version : params.version with
      | v1 definitions repetitions =>
        simp only [version] at read ⊢
        obtain ⟨_, _, size, _, wire⟩ := decodePayload_sound read
        simp only [ScalarPage.Limits.payloadBounds, Nat.sub_zero] at size
        exact ⟨size, size ▸ outputCap, wire⟩
      | v2 nulls rows repetitions definitions flag =>
        simp only [version] at read ⊢
        cases sliced : ScalarPage.splitV2 params.sizes pageLimits.levels.bytes repetitions definitions source with
        | error _ => simp [sliced] at read
        | ok pair =>
          obtain ⟨levels, encoded⟩ := pair
          obtain ⟨rep, comp, uncomp, _, levelCap, levelSize, sourceParts⟩ := ScalarPage.splitV2_ok_iff.mp sliced
          simp only [sliced] at read
          obtain ⟨plain, payload, outputParts⟩ := append_ok read
          have parts : encoded.length = params.sizes.compressed - definitions ∧
              plain.length = params.sizes.uncompressed - definitions ∧
              (if flag.getD true then StreamWire limits encoded plain else plain = encoded) := by
            cases flagValue : flag.getD true
            · simp only [ScalarPage.v2Codec, flagValue, Bool.false_eq_true, ↓reduceIte] at payload ⊢
              cases raw : Payload.decode (pageLimits.payloadBounds params.sizes definitions)
                  Payload.Codec.uncompressed.id encoded with
              | error _ => simp [raw] at payload
              | ok value =>
                simp only [raw, Except.ok.injEq] at payload
                subst value
                exact raw_sound raw
            · have expanded : decodePayload limits (pageLimits.payloadBounds params.sizes definitions)
                  encoded = .ok plain := by
                simpa [ScalarPage.v2Codec, flagValue, codec, Payload.Codec.id] using payload
              obtain ⟨inputSize, _, outputSize, _, wire⟩ := decodePayload_sound expanded
              exact ⟨inputSize, outputSize, by simpa only [flagValue, ↓reduceIte] using wire⟩
          obtain ⟨encodedSize, plainSize, wire⟩ := parts
          have fullSize : output.length = params.sizes.uncompressed := by
            rw [outputParts, List.length_append, Bytes.length_toList, levelSize, plainSize]
            omega
          exact ⟨fullSize, fullSize ▸ outputCap, rep, comp, uncomp, levelCap,
            levels.toList, encoded, plain, by simpa using levelSize, sourceParts, outputParts,
            encodedSize, plainSize, wire⟩
  · simp [codec] at read

end Silmaril.Proofs.Formats.Parquet.ScalarPage.BrotliRaw
