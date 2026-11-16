module

public import Silmaril.Formats.Cbor.Deterministic.Defs
public import Silmaril.Formats.Cbor.Value.Thms

/-! # Proofs: deterministic CBOR (`Silmaril.Formats.Cbor.Deterministic.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Cbor.Deterministic

open Silmaril.Formats.Cbor Silmaril.Formats.Cbor.Deterministic

mutual

theorem encodable_of_detOk {P : DetProfile} (v : Value) (h : detOk P v = true) : v.Encodable := by
  match v, h with
  | .uint _, h | .nint _, h | .bytes _, h =>
    simp only [detOk, decide_eq_true_eq] at h
    exact h
  | .text _, h =>
    simp only [detOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  | .array xs, h =>
    simp only [detOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, listEncodable_of_detOkList xs h.2⟩
  | .map kvs, h =>
    simp only [detOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, mapEncodable_of_detOkMap kvs h.1.2⟩
  | .tag _ w, h =>
    simp only [detOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, encodable_of_detOk w h.2⟩
  | .simple _, h =>
    simp only [detOk, decide_eq_true_eq] at h
    exact h
  | .float _ _, h =>
    simp only [detOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

theorem listEncodable_of_detOkList {P : DetProfile} (xs : List Value)
    (h : detOkList P xs = true) : ListEncodable xs := by
  match xs, h with
  | [], _ => trivial
  | x :: xs, h =>
    simp only [detOkList, Bool.and_eq_true] at h
    exact ⟨encodable_of_detOk x h.1, listEncodable_of_detOkList xs h.2⟩

theorem mapEncodable_of_detOkMap {P : DetProfile} (kvs : List (Value × Value))
    (h : detOkMap P kvs = true) : MapEncodable kvs := by
  match kvs, h with
  | [], _ => trivial
  | (k, v) :: kvs, h =>
    simp only [detOkMap, Bool.and_eq_true] at h
    exact ⟨encodable_of_detOk k h.1.1, encodable_of_detOk v h.1.2, mapEncodable_of_detOkMap kvs h.2⟩

end

theorem check_iff {P : DetProfile} {w : List UInt8} : check P w = true ↔ w ∈ language P := by
  constructor
  · intro h
    unfold check at h
    split at h
    · next v _ =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨v, h.1, h.2⟩
    · simp at h
  · rintro ⟨v, hok, rfl⟩
    simp [check, decode_encode v (encodable_of_detOk v hok), hok]

theorem language_le_wellFormed (P : DetProfile) : language P ≤ wellFormed := by
  rintro w ⟨v, hok, rfl⟩
  exact encode_mem_wellFormed v (encodable_of_detOk v hok)

theorem value_unique {P : DetProfile} {v v' : Value} (h : detOk P v = true)
    (h' : detOk P v' = true) (he : v.encode = v'.encode) : v = v' :=
  encode_injective (encodable_of_detOk v h) (encodable_of_detOk v' h') he

mutual

theorem detOk_mono {P Q : DetProfile} (hf : ∀ w b, P.floatOk w b = true → Q.floatOk w b = true)
    (hu : Q.utf8Text = true → P.utf8Text = true) (v : Value) (h : detOk P v = true) :
    detOk Q v = true := by
  match v, h with
  | .uint _, h | .nint _, h | .bytes _, h | .simple _, h => simpa [detOk] using h
  | .text t, h =>
    simp only [detOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h ⊢
    refine ⟨h.1, ?_⟩
    cases hq : Q.utf8Text
    · exact Or.inl rfl
    · rcases h.2 with h2 | h2
      · rw [hu hq] at h2; cases h2
      · exact Or.inr h2
  | .array xs, h =>
    simp only [detOk, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, detOkList_mono hf hu xs h.2⟩
  | .map kvs, h =>
    simp only [detOk, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, detOkMap_mono hf hu kvs h.1.2⟩, h.2⟩
  | .tag _ w, h =>
    simp only [detOk, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, detOk_mono hf hu w h.2⟩
  | .float w b, h =>
    simp only [detOk, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, hf w b h.2⟩

theorem detOkList_mono {P Q : DetProfile} (hf : ∀ w b, P.floatOk w b = true → Q.floatOk w b = true)
    (hu : Q.utf8Text = true → P.utf8Text = true) (xs : List Value) (h : detOkList P xs = true) :
    detOkList Q xs = true := by
  match xs, h with
  | [], _ => rfl
  | x :: xs, h =>
    simp only [detOkList, Bool.and_eq_true] at h ⊢
    exact ⟨detOk_mono hf hu x h.1, detOkList_mono hf hu xs h.2⟩

theorem detOkMap_mono {P Q : DetProfile} (hf : ∀ w b, P.floatOk w b = true → Q.floatOk w b = true)
    (hu : Q.utf8Text = true → P.utf8Text = true) (kvs : List (Value × Value))
    (h : detOkMap P kvs = true) : detOkMap Q kvs = true := by
  match kvs, h with
  | [], _ => rfl
  | (k, v) :: kvs, h =>
    simp only [detOkMap, Bool.and_eq_true] at h ⊢
    exact ⟨⟨detOk_mono hf hu k h.1.1, detOk_mono hf hu v h.1.2⟩, detOkMap_mono hf hu kvs h.2⟩

end

theorem language_mono {P Q : DetProfile} (hf : ∀ w b, P.floatOk w b = true → Q.floatOk w b = true)
    (hu : Q.utf8Text = true → P.utf8Text = true) : language P ≤ language Q := by
  rintro w ⟨v, hok, rfl⟩
  exact ⟨v, detOk_mono hf hu v hok, rfl⟩

/-! ## DRISL is deterministic with 64-bit floats and UTF-8 text -/

mutual

theorem detOk_of_drisl {P : Drisl.Profile} (v : Value) (h : Drisl.ok P v = true) :
    detOk ⟨FloatRule.only64, true⟩ v = true := by
  match v, h with
  | .uint _, h | .nint _, h =>
    simp only [Drisl.ok, Drisl.okInt, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa [detOk] using h.1
  | .bytes _, h => simpa [detOk, Drisl.ok] using h
  | .text _, h =>
    simp only [Drisl.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [detOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_true, Bool.false_or]
    exact ⟨h.1, h.2⟩
  | .array xs, h =>
    simp only [Drisl.ok, Bool.and_eq_true] at h
    simp only [detOk, Bool.and_eq_true]
    exact ⟨h.1, detOkList_of_drisl xs h.2⟩
  | .map kvs, h =>
    simp only [Drisl.ok, Bool.and_eq_true] at h
    simp only [detOk, Bool.and_eq_true]
    exact ⟨⟨h.1.1, detOkMap_of_drisl kvs h.1.2⟩, h.2⟩
  | .tag n c, h =>
    by_cases hn : n = 42
    · subst hn
      cases c with
      | bytes b =>
        simp only [Drisl.ok, Bool.and_eq_true, decide_eq_true_eq] at h
        simp only [detOk, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by decide, h.1⟩
      | _ => simp [Drisl.ok] at h
    · simp [Drisl.ok, hn] at h
  | .simple n, h =>
    simp only [Drisl.ok, Bool.or_eq_true, beq_iff_eq] at h
    simp only [detOk, decide_eq_true_eq]
    omega
  | .float w bits, h =>
    simp only [Drisl.ok, Drisl.okFloat64, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨_, rfl⟩, ⟨hb, _⟩, _⟩ := h
    simp only [detOk, FloatRule.only64, Bool.and_eq_true, decide_eq_true_eq, beq_self_eq_true,
      and_true]
    exact ⟨Or.inr (Or.inr trivial), hb⟩

theorem detOkList_of_drisl {P : Drisl.Profile} (xs : List Value) (h : Drisl.okList P xs = true) :
    detOkList ⟨FloatRule.only64, true⟩ xs = true := by
  match xs, h with
  | [], _ => rfl
  | x :: xs, h =>
    simp only [Drisl.okList, Bool.and_eq_true] at h
    simp only [detOkList, Bool.and_eq_true]
    exact ⟨detOk_of_drisl x h.1, detOkList_of_drisl xs h.2⟩

theorem detOkMap_of_drisl {P : Drisl.Profile} (kvs : List (Value × Value))
    (h : Drisl.okMap P kvs = true) : detOkMap ⟨FloatRule.only64, true⟩ kvs = true := by
  match kvs, h with
  | [], _ => rfl
  | (k, v) :: kvs, h =>
    simp only [Drisl.okMap, Bool.and_eq_true] at h
    simp only [detOkMap, Bool.and_eq_true]
    exact ⟨⟨detOk_of_drisl k h.1.1.2, detOk_of_drisl v h.1.2⟩, detOkMap_of_drisl kvs h.2⟩

end

theorem drisl_le (P : Drisl.Profile) : Drisl.language P ≤ language ⟨FloatRule.only64, true⟩ := by
  rintro w ⟨v, hok, rfl⟩
  exact ⟨v, detOk_of_drisl v hok, rfl⟩

end Silmaril.Proofs.Formats.Cbor.Deterministic

end
