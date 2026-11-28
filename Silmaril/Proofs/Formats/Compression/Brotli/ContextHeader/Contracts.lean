module

public import Silmaril.Formats.Compression.Brotli.ContextHeader.Defs
import Silmaril.Formats.Compression.Brotli.BlockTypes.Thms
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.ContextHeader

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.ContextHeader
open Silmaril.Formats.Compression.Brotli.ContextHeader.Internal

theorem Fields.ranges (fields : Fields) :
    fields.postfixBits.val ≤ 3 ∧ fields.directField.val ≤ 15 ∧
    fields.direct ≤ 120 ∧ fields.direct % (2 ^ fields.postfixBits.val) = 0 ∧
    64 ≤ fields.distanceAlphabet ∧ fields.distanceAlphabet ≤ 520 := by
  have postfixBits := fields.postfixBits.isLt
  have direct := fields.directField.isLt
  have scaleHi : 2 ^ fields.postfixBits.val ≤ 8 := Nat.pow_le_pow_right (show 0 < (2 : Nat) by decide) (show fields.postfixBits.val ≤ 3 by omega)
  have scaleLo : 1 ≤ 2 ^ fields.postfixBits.val := Nat.two_pow_pos _
  have scaled : fields.direct ≤ 120 := by
    unfold Fields.direct
    exact Nat.le_trans (Nat.mul_le_mul_right _ (show fields.directField.val ≤ 15 by omega))
      (Nat.mul_le_mul_left 15 scaleHi)
  exact ⟨by omega, by omega, scaled, by simp [Fields.direct],
    by unfold Fields.distanceAlphabet; omega, by unfold Fields.distanceAlphabet; omega⟩

private structure Advance (before after : LSBReader) (input used suffix : List Bool) : Prop where
  split : input = used ++ suffix
  rep : after.Rep suffix
  buffered : after.count < 8
  offset : after.totalRead = before.totalRead + used.length

private theorem Advance.trans {before middle after : LSBReader} {input a rest b suffix : List Bool}
    (first : Advance before middle input a rest) (second : Advance middle after rest b suffix) :
    Advance before after input (a ++ b) suffix := by
  refine ⟨by rw [first.split, second.split, List.append_assoc], second.rep, second.buffered, ?_⟩
  simp only [List.length_append, first.offset, second.offset]
  omega

private theorem bind_ok {α β : Type} {action : Except Error α} {next : α → Except Error β}
    {value : β} (read : (action >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases read
  | ok value => exact ⟨value, rfl, read⟩

private theorem take_sound {width value : Nat} {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (read : take before width = .ok (value, after)) :
    value < 2 ^ width ∧ ∃ suffix, Advance before after input (natBits value width) suffix := by
  unfold take at read
  split at read <;> try contradiction
  rename_i pair actual
  cases read
  obtain ⟨suffix, split, rep', fits, offset, count'⟩ := LSBReader.readBits_sound rep count actual
  exact ⟨fits, suffix, split, rep', count' ▸ Nat.mod_lt _ (by decide),
    by simpa only [natBits_length] using offset⟩

private theorem mode_code (code : Nat) (fits : code < 4) : (mode code).code = code := by
  have values : code = 0 ∨ code = 1 ∨ code = 2 ∨ code = 3 := by omega
  rcases values with rfl | rfl | rfl | rfl <;> rfl

private theorem modes_sound {n : Nat} {before after : LSBReader}
    {input : List Bool} {modes : List Mode} (rep : before.Rep input) (count : before.count < 8)
    (read : readModes n before = .ok (modes, after)) :
    modes.length = n ∧ ∃ suffix, Advance before after input
      (modes.flatMap fun mode => natBits mode.code 2) suffix := by
  induction n generalizing before after input modes with
  | zero =>
    simp only [readModes, Except.ok.injEq, Prod.mk.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    exact ⟨rfl, input, rfl, rep, count, by simp⟩
  | succ n ih =>
    simp only [readModes] at read
    obtain ⟨⟨code, middle⟩, field, next⟩ := bind_ok read
    obtain ⟨⟨tail, last⟩, more, done⟩ := bind_ok next
    cases done
    obtain ⟨fits, rest, first⟩ := take_sound rep count field
    obtain ⟨size, suffix, second⟩ := ih first.rep first.buffered more
    refine ⟨by simp [size], suffix, ?_⟩
    simpa only [List.flatMap_cons, mode_code code fits] using first.trans second

private theorem mode_bits_length (modes : List Mode) :
    (modes.flatMap fun mode => natBits mode.code 2).length = 2 * modes.length := by
  induction modes with
  | nil => rfl
  | cons mode rest ih =>
    simp only [List.flatMap_cons, List.length_append, natBits_length, List.length_cons, ih]
    omega

theorem Wire.length {types : Nat} {bits : List Bool} {fields : Fields} (wire : Wire types bits fields) :
    bits.length = 6 + 2 * types := by
  obtain ⟨_, _, modeCount, rfl⟩ := wire
  simp only [Fields.bits, List.length_append, natBits_length, mode_bits_length, modeCount]

theorem readAfter_sound {types bitLimit : Nat} {before after : LSBReader} {input : List Bool}
    {fields : Fields} (rep : before.Rep input) (count : before.count < 8)
    (read : readAfter types bitLimit before = .ok (fields, after)) :
    ∃ used suffix, Wire types used fields ∧ input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + (6 + 2 * types) ∧ used.length ≤ bitLimit := by
  unfold readAfter at read
  split at read <;> try contradiction
  rename_i typeCap
  split at read <;> try contradiction
  rename_i bitCap
  obtain ⟨⟨postfixBits, next⟩, postRead, more⟩ := bind_ok read
  obtain ⟨⟨direct, next'⟩, directRead, more⟩ := bind_ok more
  obtain ⟨⟨modes, last⟩, modesRead, done⟩ := bind_ok more
  cases done
  obtain ⟨postFit, tail, first⟩ := take_sound rep count postRead
  obtain ⟨directFit, modeBits, second⟩ := take_sound first.rep first.buffered directRead
  obtain ⟨size, suffix, third⟩ := modes_sound second.rep second.buffered modesRead
  have all := (first.trans second).trans third
  refine ⟨_, suffix, ⟨by omega, by omega, size, ?_⟩, all.split, all.rep, all.buffered, ?_, ?_⟩
  · simp [Fields.bits, Fin.ofNat, Nat.mod_eq_of_lt postFit, Nat.mod_eq_of_lt directFit]
  · simpa only [List.length_append, natBits_length, mode_bits_length, size, show 2 + 4 = 6 by decide]
      using all.offset
  · simp only [List.length_append, natBits_length, mode_bits_length, size]
    omega

private theorem controls_ok {α : Type} {action : Except BlockTypes.Error α} {out : α}
    (read : action.mapError Error.controls = .ok out) : action = .ok out := by
  cases action <;> cases read <;> rfl

theorem read_sound {bitLimit : Nat} {before after : LSBReader} {input : List Bool}
    {header : Header} (rep : before.Rep input) (count : before.count < 8)
    (read : read bitLimit before = .ok (header, after)) :
    ∃ used suffix postControls,
      Header.Wire used header ∧ input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      BlockTypes.read bitLimit before = .ok (header.controls, postControls) ∧
      after.totalRead = postControls.totalRead + (6 + 2 * header.controls.literal.typeCount) ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit := by
  unfold Formats.Compression.Brotli.ContextHeader.read at read
  obtain ⟨⟨controls, postControls⟩, controlRead, next⟩ := bind_ok read
  obtain ⟨⟨fields, last⟩, fieldRead, done⟩ := bind_ok next
  cases done
  have controlRead := controls_ok controlRead
  obtain ⟨pre, rest, controlWire, split, rep', count', offset, cap⟩ := BlockTypes.read_sound rep count controlRead
  obtain ⟨body, suffix, bodyWire, split', rep'', count'', offset', cap'⟩ := readAfter_sound rep' count' fieldRead
  have size := Wire.length bodyWire
  refine ⟨pre ++ body, suffix, postControls, ⟨pre, body, rfl, controlWire, bodyWire⟩, ?_,
    rep'', count'', controlRead, offset', ?_, ?_⟩
  · rw [split, split', List.append_assoc]
  · simp only [List.length_append]
    omega
  · simp only [List.length_append]
    omega

end Silmaril.Proofs.Formats.Compression.Brotli.ContextHeader
