module

public import Silmaril.Formats.Bao.Defs

public section

namespace Silmaril.Proofs.Formats.Bao

open Silmaril.Formats.Bao

theorem putLE_length (width size : Nat) : (putLE width size).length = width := by
  induction width generalizing size with
  | zero => rfl
  | succ width ih => simp [putLE, ih]

theorem getLE_bound (header : Bytes) : getLE header < 256 ^ header.length := by
  induction header with
  | nil => decide
  | cons byte rest ih =>
    have range := UInt8.toNat_lt byte
    simp only [getLE, List.length_cons, Nat.pow_succ']
    omega

theorem getLE_putLE {width size : Nat} (range : size < 256 ^ width) :
    getLE (putLE width size) = size := by
  induction width generalizing size with
  | zero => have : size = 0 := by simpa using range
            simp [putLE, getLE, this]
  | succ width ih =>
    have quotient : size / 256 < 256 ^ width := by
      simp only [Nat.pow_succ'] at range
      omega
    simp only [putLE, getLE, UInt8.toNat_ofNat', ih quotient]
    omega

theorem takeExact_spec {width : Nat} {input field rest : Bytes} :
    takeExact width input = some (field, rest) ↔ field.length = width ∧ input = field ++ rest := by
  constructor
  · intro parsed
    simp only [takeExact] at parsed
    split at parsed
    · next lengthEq =>
      cases parsed
      exact ⟨lengthEq, (List.take_append_drop _ _).symm⟩
    · contradiction
  · rintro ⟨lengthEq, rfl⟩
    simp [takeExact, ← lengthEq]

theorem readHeader_spec {input rest : Bytes} {size : Nat} :
    readHeader input = some (size, rest) ↔
      ∃ header : Bytes, header.length = 8 ∧ getLE header = size ∧ input = header ++ rest := by
  constructor
  · intro parsed
    cases header : takeExact 8 input with
    | none => simp [readHeader, header] at parsed
    | some pair =>
      obtain ⟨field, tail⟩ := pair
      simp [readHeader, header] at parsed
      obtain ⟨lengthEq, inputEq⟩ := takeExact_spec.mp header
      exact ⟨field, lengthEq, parsed.1, by simpa [parsed.2] using inputEq⟩
  · rintro ⟨header, width, lengthEq, inputEq⟩
    have head := takeExact_spec.mpr ⟨width, inputEq⟩
    simp [readHeader, head, lengthEq]

theorem readHeader_bound {input rest : Bytes} {size : Nat}
    (parsed : readHeader input = some (size, rest)) : size < u64Limit := by
  rcases readHeader_spec.mp parsed with ⟨header, width, rfl, _⟩
  simpa only [width, u64Limit, show (256 : Nat)^8 = 2^64 by decide] using getLE_bound header

theorem readHeader_putLE64 {size : Nat} (body : Bytes) (range : size < u64Limit) :
    readHeader (putLE64 size ++ body) = some (size, body) :=
  readHeader_spec.mpr ⟨putLE64 size, putLE_length 8 size, getLE_putLE range, rfl⟩

theorem readSlots_spec {layout : List Slot} {fields : List Bytes} {input rest : Bytes} :
    readSlots layout input = some (fields, rest) ↔
      Tape layout fields ∧ input = fields.flatten ++ rest := by
  induction layout generalizing fields input rest with
  | nil => cases fields <;> simp [readSlots, Tape, eq_comm]
  | cons slot layout ih =>
    constructor
    · intro parsed
      cases head : takeExact slot.width input with
      | none => simp [readSlots, head] at parsed
      | some pair =>
        obtain ⟨field, tail⟩ := pair
        cases suffix : readSlots layout tail with
        | none => simp [readSlots, head, suffix] at parsed
        | some pair =>
          obtain ⟨cells, remaining⟩ := pair
          have ⟨lengthEq, inputEq⟩ := takeExact_spec.mp head
          have ⟨tape, tailEq⟩ := ih.mp suffix
          simp [readSlots, head, suffix] at parsed
          obtain ⟨rfl, rfl⟩ := parsed
          exact ⟨⟨lengthEq, tape⟩, by simp [inputEq, tailEq, List.append_assoc]⟩
    · cases fields with
      | nil => simp [Tape]
      | cons field fields =>
        rintro ⟨⟨widthEq, tape⟩, inputEq⟩
        have head : takeExact slot.width input = some (field, fields.flatten ++ rest) :=
          takeExact_spec.mpr ⟨widthEq, by simpa [List.append_assoc] using inputEq⟩
        have suffix := (ih (rest := rest)).mpr ⟨tape, rfl⟩
        simp [readSlots, head, suffix]

theorem readFrame_spec {layout : List Slot} {fields : List Bytes} {input : Bytes} :
    readFrame layout input = some fields ↔ Tape layout fields ∧ input = fields.flatten := by
  constructor
  · intro parsed
    cases body : readSlots layout input with
    | none => simp [readFrame, body] at parsed
    | some pair =>
      obtain ⟨cells, remainder⟩ := pair
      have ⟨tape, inputEq⟩ := readSlots_spec.mp body
      simp [readFrame, body] at parsed
      obtain ⟨rfl, rfl⟩ := parsed
      exact ⟨tape, by simpa using inputEq⟩
  · rintro ⟨tape, rfl⟩
    have body : readSlots layout fields.flatten = some (fields, []) :=
      readSlots_spec.mpr ⟨tape, by simp⟩
    simp [readFrame, body]

theorem decode_spec {encoding : Encoding} {size : Nat} {input : Bytes} {fields : List Bytes} :
    decode encoding input = some (size, fields) ↔
      encoding.valid = true ∧ encoding.bodyFits size fields.flatten.length = true ∧
      readHeader input = some (size, fields.flatten) ∧ Tape (encoding.layout size) fields := by
  constructor
  · intro decoded
    cases allowed : encoding.valid <;> simp [decode, allowed] at decoded
    cases header : readHeader input with
    | none => simp [header] at decoded
    | some pair =>
      obtain ⟨claim, body⟩ := pair
      cases fits : encoding.bodyFits claim body.length <;> simp [header, fits] at decoded
      cases parsed : readFrame (encoding.layout claim) body with
      | none => simp [parsed] at decoded
      | some fieldsFound =>
        simp [parsed] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        obtain ⟨tape, rfl⟩ := readFrame_spec.mp parsed
        exact ⟨rfl, fits, rfl, tape⟩
  · rintro ⟨allowed, fits, header, tape⟩
    have parsed := readFrame_spec.mpr ⟨tape, rfl⟩
    have fits' : encoding.bodyFits size (fields.map List.length).sum = true := by simpa using fits
    simp [decode, allowed, header, fits', parsed]

theorem pairs_perm (tree : Plan) : (tree.pairs true).Perm (tree.pairs false) := by
  induction tree with
  | skip => simp [Plan.pairs]
  | leaf => simp [Plan.pairs]
  | fork span left right leftIH rightIH =>
    simp only [Plan.pairs, ite_true, Bool.false_eq_true, ite_false]
    exact ((leftIH.append rightIH).append_right [.pair span]).trans List.perm_append_comm

theorem detach_spec {layout : List Slot} {fields : List Bytes} :
    Tape layout fields ↔ ∃ proof : Detached layout,
      detach layout fields = some proof ∧ proof.fields = fields := by
  induction layout generalizing fields with
  | nil => cases fields <;> simp [Tape, detach, Detached.fields]
  | cons slot layout ih =>
    cases fields with
    | nil => simp [Tape, detach]
    | cons field tail =>
      by_cases width : field.length = slot.width
      · constructor
        · rintro ⟨_, tape⟩
          obtain ⟨proof, accepted, original⟩ := ih.mp tape
          exact ⟨.cons slot ⟨field.toArray, by simpa using width⟩ proof,
            by simp [detach, width, accepted], by simp [Detached.fields, original]⟩
        · rintro ⟨proof, accepted, original⟩
          cases rest : detach layout tail with
          | none => simp [detach, width, rest] at accepted
          | some detached =>
            have fieldsEq : detached.fields = tail := by
              simp [detach, width, rest] at accepted
              subst proof
              exact (List.cons.inj original).2
            exact ⟨width, ih.mpr ⟨detached, rest, fieldsEq⟩⟩
      · simp [Tape, detach, width]

end Silmaril.Proofs.Formats.Bao
