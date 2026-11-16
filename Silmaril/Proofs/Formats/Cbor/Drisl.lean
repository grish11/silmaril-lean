module

public import Silmaril.Formats.Cbor.Drisl.Defs
public import Silmaril.Formats.Cbor.Value.Thms

/-! # Proofs: DRISL and the ATProto core (`Silmaril.Formats.Cbor.Drisl.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Cbor.Drisl

open Silmaril.Formats.Cbor Silmaril.Formats.Cbor.Drisl

mutual

theorem encodable_of_ok {P : Profile} (v : Value) (h : ok P v = true) : v.Encodable := by
  match v, h with
  | .uint n, h | .nint n, h =>
    simp only [ok, okInt, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  | .bytes b, h =>
    simp only [ok, decide_eq_true_eq] at h
    exact h
  | .text t, h =>
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  | .array xs, h =>
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, listEncodable_of_okList xs h.2⟩
  | .map kvs, h =>
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, mapEncodable_of_okMap kvs h.1.2⟩
  | .tag n c, h =>
    by_cases hn : n = 42
    · subst hn
      cases c with
      | bytes b =>
        simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨by decide, h.1⟩
      | _ => simp [ok] at h
    · simp [ok, hn] at h
  | .simple n, h =>
    simp only [ok, Bool.or_eq_true, beq_iff_eq] at h
    exact Or.inl (by omega)
  | .float w bits, h =>
    simp only [ok, okFloat64, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨_, rfl⟩, ⟨hb, _⟩, _⟩ := h
    exact ⟨Or.inr (Or.inr rfl), by simpa using hb⟩

theorem listEncodable_of_okList {P : Profile} (xs : List Value) (h : okList P xs = true) :
    ListEncodable xs := by
  match xs, h with
  | [], _ => trivial
  | x :: xs, h =>
    simp only [okList, Bool.and_eq_true] at h
    exact ⟨encodable_of_ok x h.1, listEncodable_of_okList xs h.2⟩

theorem mapEncodable_of_okMap {P : Profile} (kvs : List (Value × Value))
    (h : okMap P kvs = true) : MapEncodable kvs := by
  match kvs, h with
  | [], _ => trivial
  | (k, v) :: kvs, h =>
    simp only [okMap, Bool.and_eq_true] at h
    exact ⟨encodable_of_ok k h.1.1.2, encodable_of_ok v h.1.2, mapEncodable_of_okMap kvs h.2⟩

end

theorem check_iff {P : Profile} {w : List UInt8} : check P w = true ↔ w ∈ language P := by
  constructor
  · intro h
    unfold check at h
    split at h
    · next v _ =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨v, h.1, h.2⟩
    · simp at h
  · rintro ⟨v, hok, rfl⟩
    simp [check, decode_encode v (encodable_of_ok v hok), hok]

theorem language_le_wellFormed (P : Profile) : language P ≤ wellFormed := by
  rintro w ⟨v, hok, rfl⟩
  exact encode_mem_wellFormed v (encodable_of_ok v hok)

theorem value_unique {P : Profile} {v v' : Value} (h : ok P v = true) (h' : ok P v' = true)
    (he : v.encode = v'.encode) : v = v' :=
  encode_injective (encodable_of_ok v h) (encodable_of_ok v' h') he

mutual

theorem ok_mono {P Q : Profile} (hf : P.floats = true → Q.floats = true)
    (hi : Q.int64 = true → P.int64 = true) (v : Value) (h : ok P v = true) : ok Q v = true := by
  match v, h with
  | .uint n, h | .nint n, h =>
    simp only [ok, okInt, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at h ⊢
    refine ⟨h.1, ?_⟩
    cases hq : Q.int64
    · exact Or.inl rfl
    · rcases h.2 with h2 | h2
      · rw [hi hq] at h2; cases h2
      · exact Or.inr h2
  | .bytes _, h | .text _, h | .simple _, h => simpa [ok] using h
  | .array xs, h =>
    simp only [ok, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, okList_mono hf hi xs h.2⟩
  | .map kvs, h =>
    simp only [ok, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, okMap_mono hf hi kvs h.1.2⟩, h.2⟩
  | .tag n c, h =>
    by_cases hn : n = 42
    · subst hn
      cases c with
      | bytes b => simpa [ok] using h
      | _ => simp [ok] at h
    · simp [ok, hn] at h
  | .float w bits, h =>
    simp only [ok, Bool.and_eq_true] at h ⊢
    exact ⟨⟨hf h.1.1, h.1.2⟩, h.2⟩

theorem okList_mono {P Q : Profile} (hf : P.floats = true → Q.floats = true)
    (hi : Q.int64 = true → P.int64 = true) (xs : List Value) (h : okList P xs = true) :
    okList Q xs = true := by
  match xs, h with
  | [], _ => rfl
  | x :: xs, h =>
    simp only [okList, Bool.and_eq_true] at h ⊢
    exact ⟨ok_mono hf hi x h.1, okList_mono hf hi xs h.2⟩

theorem okMap_mono {P Q : Profile} (hf : P.floats = true → Q.floats = true)
    (hi : Q.int64 = true → P.int64 = true) (kvs : List (Value × Value))
    (h : okMap P kvs = true) : okMap Q kvs = true := by
  match kvs, h with
  | [], _ => rfl
  | (k, v) :: kvs, h =>
    simp only [okMap, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨h.1.1.1, ok_mono hf hi k h.1.1.2⟩, ok_mono hf hi v h.1.2⟩, okMap_mono hf hi kvs h.2⟩

end

theorem language_mono {P Q : Profile} (hf : P.floats = true → Q.floats = true)
    (hi : Q.int64 = true → P.int64 = true) : language P ≤ language Q := by
  rintro w ⟨v, hok, rfl⟩
  exact ⟨v, ok_mono hf hi v hok, rfl⟩

end Silmaril.Proofs.Formats.Cbor.Drisl

end
