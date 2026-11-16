module

public import Silmaril.Formats.Cbor.ModelValid.Defs
public import Silmaril.Formats.Cbor.Value.Thms

/-! # Proofs: model-relative CBOR validity (`Silmaril.Formats.Cbor.ModelValid.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Cbor.ModelValid

open Silmaril.Formats.Cbor Silmaril.Formats.Cbor.ModelValid

mutual

theorem encodableB_iff (v : Value) : encodableB v = true ↔ v.Encodable := by
  match v with
  | .uint _ | .nint _ | .bytes _ | .text _ | .simple _ | .float _ _ =>
    simp [encodableB, Value.Encodable]
  | .array xs =>
    simp only [encodableB, Bool.and_eq_true, decide_eq_true_eq, Value.Encodable,
      encodableListB_iff xs]
  | .map kvs =>
    simp only [encodableB, Bool.and_eq_true, decide_eq_true_eq, Value.Encodable,
      encodableMapB_iff kvs]
  | .tag _ w =>
    simp only [encodableB, Bool.and_eq_true, decide_eq_true_eq, Value.Encodable, encodableB_iff w]

theorem encodableListB_iff (xs : List Value) : encodableListB xs = true ↔ ListEncodable xs := by
  match xs with
  | [] => simp [encodableListB, ListEncodable]
  | x :: xs =>
    simp only [encodableListB, Bool.and_eq_true, ListEncodable, encodableB_iff x,
      encodableListB_iff xs]

theorem encodableMapB_iff (kvs : List (Value × Value)) :
    encodableMapB kvs = true ↔ MapEncodable kvs := by
  match kvs with
  | [] => simp [encodableMapB, MapEncodable]
  | (k, v) :: kvs =>
    simp only [encodableMapB, Bool.and_eq_true, MapEncodable, encodableB_iff k, encodableB_iff v,
      encodableMapB_iff kvs, and_assoc]

end

theorem check_iff {w : List UInt8} : check w = true ↔ w ∈ language := by
  constructor
  · intro h
    unfold check at h
    split at h
    · next v _ =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨v, (encodableB_iff v).mp h.1.1, h.1.2, h.2⟩
    · simp at h
  · rintro ⟨v, he, hok, rfl⟩
    simp [check, decode_encode v he, (encodableB_iff v).mpr he, hok]

theorem language_le_wellFormed : language ≤ wellFormed := by
  rintro w ⟨v, he, -, rfl⟩
  exact encode_mem_wellFormed v he

end Silmaril.Proofs.Formats.Cbor.ModelValid

end
