module

public import Silmaril.Formats.ColumnarTimestamp.Wire.Defs
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Numeric.Timestamp.Thms
import Silmaril.Prelude.Bytes.Digits.Thms
import Init.Data.SInt.Lemmas

namespace Silmaril.Proofs.Formats.ColumnarTimestamp.Wire

open Silmaril.Formats Silmaril.Formats.ColumnarTimestamp Silmaril.Numeric.Timestamp
open Silmaril.Formats.Parquet

variable {kind : Kind} {source target : TickUnit}

private theorem decodeInt64_word_inverse (word : List UInt8) (width : word.length = 8) :
    Plain.writeUInt64Word (Plain.readUInt64Word word).toInt64.toUInt64 = word := by
  have unpacked : KBytes.unpack 8 (KBytes.leVal word) = word := by
    simpa only [width] using KBytes.unpack_leVal word
  have fits : KBytes.leVal word % 256 ^ 8 = KBytes.leVal word := by
    rw [← KBytes.leVal_unpack, unpacked]
  simp only [Plain.writeUInt64Word, Plain.readUInt64Word, UInt64.toUInt64_toInt64]
  change KBytes.unpack 8 (KBytes.leVal word % 256 ^ 8) = word
  rw [fits, unpacked]

private theorem decodeInt64_exact {bytes : Bytes} {count : Nat} {words : List Int64}
    (decoded : Plain.decodeInt64 count bytes = .ok words) :
    words.length = count ∧ Plain.encodeInt64 words = bytes := by
  obtain ⟨_, chunks, octets, length, widths, rfl⟩ := Plain.decodeFixedWidth_ok_iff.mp decoded
  refine ⟨by simpa using length, Bytes.ext ?_⟩
  have rebuilt : chunks.map (fun word =>
      Plain.writeUInt64Word (Plain.readUInt64Word word).toInt64.toUInt64) = chunks := by
    simpa using (List.map_congr_left (g := id) fun word mem => decodeInt64_word_inverse word (widths word mem))
  simpa only [Plain.encodeInt64, Plain.encodeWords, Bytes.toList_ofList, List.flatMap,
    List.map_map, Function.comp_def, rebuilt] using octets.symm

private theorem encoded_denotes {values : List (Ticks kind source)} {words : List Int64}
    (encoded : values.mapM (fun value => Ticks.toInt64 value target) = .ok words) :
    (words.map (fun word => (Ticks.ofInt64 kind target word).denote)) = values.map Ticks.denote := by
  induction values generalizing words with
  | nil => cases encoded; rfl
  | cons value rest ih =>
    rw [List.mapM_cons] at encoded
    cases first : value.toInt64 target with
    | error e => simp [first, bind, Except.bind] at encoded
    | ok word =>
      cases remaining : rest.mapM (fun value => Ticks.toInt64 value target) with
      | error e => simp [first, remaining, bind, Except.bind] at encoded
      | ok tail =>
        simp only [first, remaining, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at encoded
        subst words
        rw [List.map_cons, List.map_cons, ih remaining, Ticks.toInt64_eq_ok_iff.mp first]

public theorem decodeLE_encodeLE {values : List (Ticks kind source)} {bytes : Bytes}
    (encoded : Wire.encodeLE target values = .ok bytes) :
    (Wire.decodeLE kind target values.length bytes).map (List.map Ticks.denote) =
      .ok (values.map Ticks.denote) := by
  cases narrowed : values.mapM (fun value => Ticks.toInt64 value target) with
  | error e => simp [Wire.encodeLE, narrowed, Except.map] at encoded
  | ok words =>
    simp only [Wire.encodeLE, narrowed, Except.map, Except.ok.injEq] at encoded
    subst bytes
    have denotations := encoded_denotes narrowed
    have count : words.length = values.length := by
      simpa only [List.length_map] using congrArg List.length denotations
    simpa only [Wire.decodeLE, ← count, Plain.decodeInt64_encodeInt64, Except.map, List.map_map,
      Except.ok.injEq, Function.comp_def] using denotations

public theorem encodeLE_isSome_iff (values : List (Ticks kind source)) :
    (Wire.encodeLE target values).toOption.isSome = true ↔
      ∀ value ∈ values, (value.toInt64 target).toOption.isSome = true := by
  unfold Wire.encodeLE
  induction values with
  | nil => simp [Except.map, Except.toOption, pure, Except.pure]
  | cons value rest ih =>
    rw [List.mapM_cons, List.forall_mem_cons]
    cases first : value.toInt64 target with
    | error e => simp [bind, Except.bind, Except.map, Except.toOption]
    | ok word =>
      cases remaining : rest.mapM (fun x => Ticks.toInt64 x target) <;>
        simpa [first, remaining, bind, Except.bind, Except.map, Except.toOption, pure, Except.pure] using ih

private theorem encodeDecoded (kind : Kind) (unit : TickUnit) (words : List Int64) :
    (words.map (Ticks.ofInt64 kind unit)).mapM (fun value => Ticks.toInt64 value unit) = .ok words := by
  simp only [List.mapM_map, Function.comp_def, Ticks.toInt64_ofInt64]
  induction words with
  | nil => rfl
  | cons word rest ih => simp [List.mapM_cons, ih, bind, Except.bind, pure, Except.pure]

public theorem encodeLE_decodeLE {bytes : Bytes} {count : Nat} {values : List (Ticks kind target)}
    (decoded : Wire.decodeLE kind target count bytes = .ok values) :
    values.length = count ∧ Wire.encodeLE target values = .ok bytes := by
  cases read : Plain.decodeInt64 count bytes with
  | error e => simp [Wire.decodeLE, read, Except.map] at decoded
  | ok words =>
    simp only [Wire.decodeLE, read, Except.map, Except.ok.injEq] at decoded
    subst values
    obtain ⟨length, reencoded⟩ := decodeInt64_exact read
    refine ⟨by simpa only [List.length_map] using length, ?_⟩
    rw [Wire.encodeLE, encodeDecoded]
    exact congrArg Except.ok reencoded

end Silmaril.Proofs.Formats.ColumnarTimestamp.Wire
