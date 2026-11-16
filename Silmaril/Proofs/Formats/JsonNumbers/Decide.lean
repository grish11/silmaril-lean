module

public import Silmaril.Formats.JsonNumbers.Defs
public import Silmaril.Formats.JsonBytes.Thms

/-! # Proofs: the decision procedure for `JsonNumbers.language` (`Silmaril.Formats.JsonNumbers.Thms`)

The proof follows `Silmaril.Proofs.Formats.JsonBytes.Decide`, with the number rule checked by
membership in the number-token language. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonNumbers.Decide

open RegularExpression Silmaril.Formats.JsonBytes Silmaril.Formats.JsonNumbers

theorem mem_splits {α : Type} {w : List α} {ab : List α × List α} :
    ab ∈ splits w ↔ ab.1 ++ ab.2 = w := by
  induction w generalizing ab with
  | nil =>
    obtain ⟨a, b⟩ := ab
    simp [splits]
  | cons x xs ih =>
    obtain ⟨a, b⟩ := ab
    simp only [splits, List.mem_cons, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨⟨a', b'⟩, h, rfl, rfl⟩)
      · rfl
      · simpa using ih.mp h
    · intro h
      cases a with
      | nil => exact Or.inl ⟨rfl, h⟩
      | cons y a =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        exact Or.inr ⟨⟨a, b⟩, ih.mpr h, rfl, rfl⟩

theorem any_splits {α : Type} {w : List α} {f : List α × List α → Bool} :
    (splits w).any f = true ↔ ∃ a b, a ++ b = w ∧ f (a, b) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨a, b⟩, h, hf⟩; exact ⟨a, b, mem_splits.mp h, hf⟩
  · rintro ⟨a, b, h, hf⟩; exact ⟨(a, b), mem_splits.mpr h, hf⟩

theorem rm {r : RegularExpression UInt8} {w : List UInt8} : r.rmatch w = true ↔ w ∈ r.matches' :=
  rmatch_iff_matches' r w

/-! ## Non-empty parts -/

theorem structural_length {c : UInt8} {w : List UInt8} (h : w ∈ (structural c).matches') :
    1 ≤ w.length := by
  simp only [structural, matches'_mul, matches'_char, Language.mem_mul] at h
  obtain ⟨a, ⟨a₁, -, a₂, ha₂, rfl⟩, b, -, rfl⟩ := h
  obtain rfl : a₂ = [c] := ha₂
  simp only [List.length_append, List.length_singleton]
  omega

theorem string_length {p : Profile} {w : List UInt8} (h : w ∈ (string p).matches') :
    1 ≤ w.length := by
  cases w with
  | cons => simp
  | nil =>
    rw [← rm] at h
    cases p <;> exact absurd h (by decide)

/-! ## Soundness -/

variable {p : Profile} {N : Language UInt8} [DecidablePred (· ∈ N)]

mutual

theorem valueB_sound : ∀ {n : Nat} {w : List UInt8}, valueB p N n w = true → Value p N w
  | 0, _, h => by simp [valueB] at h
  | n + 1, w, h => by
    simp only [valueB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm, decide_eq_true_eq] at h
    rcases h with (hs | hn) | ⟨a, r, rfl, h⟩
    · exact .literal hs
    · exact .number hn
    rcases h with ⟨ha, m, b, rfl, hb, hm⟩ | ⟨ha, m, b, rfl, hb, hm⟩
    · rcases hm with hm | hm
      · rw [List.isEmpty_iff.mp hm, List.nil_append]
        exact .emptyArray ha hb
      · rw [← List.append_assoc]
        exact .array ha (elementsB_sound hm) hb
    · rcases hm with hm | hm
      · rw [List.isEmpty_iff.mp hm, List.nil_append]
        exact .emptyObject ha hb
      · rw [← List.append_assoc]
        exact .object ha (membersB_sound hm) hb

theorem elementsB_sound : ∀ {n : Nat} {w : List UInt8}, elementsB p N n w = true → Elements p N w
  | 0, _, h => by simp [elementsB] at h
  | n + 1, w, h => by
    simp only [elementsB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm] at h
    rcases h with hv | ⟨v, r, rfl, hv, s, vs, rfl, hs, hx⟩
    · exact .one (valueB_sound hv)
    · rw [← List.append_assoc]
      exact .cons (valueB_sound hv) hs (elementsB_sound hx)

theorem membersB_sound : ∀ {n : Nat} {w : List UInt8}, membersB p N n w = true → Members p N w
  | 0, _, h => by simp [membersB] at h
  | n + 1, w, h => by
    simp only [membersB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm] at h
    obtain ⟨m, r, rfl, ⟨k, kr, rfl, hk, c, v, rfl, hc, hv⟩, hr⟩ := h
    rcases hr with hr | ⟨s, ms, rfl, hs, hm⟩
    · rw [List.isEmpty_iff.mp hr, List.append_nil, ← List.append_assoc]
      exact .one hk hc (valueB_sound hv)
    · simp only [← List.append_assoc]
      exact .cons hk hc (valueB_sound hv) hs (membersB_sound hm)

end

/-! ## Completeness -/

theorem succ_of_le {n m : Nat} (h : m + 1 ≤ n) : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩

mutual

theorem valueB_complete {w : List UInt8} :
    Value p N w → ∀ n, 2 * w.length + 1 ≤ n → valueB p N n w = true
  | .literal hs, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    simp [valueB, rm.mpr hs]
  | .number hs, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    simp [valueB, hs]
  | .emptyArray (a := a) (b := b) ha hb, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    simp only [valueB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm]
    exact Or.inr ⟨a, b, rfl, Or.inl ⟨ha, [], b, rfl, hb, Or.inl rfl⟩⟩
  | .array (a := a) (xs := xs) (b := b) ha hx hb, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    have h1 := structural_length ha; have h2 := structural_length hb
    simp only [List.length_append] at hn
    simp only [valueB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm]
    exact Or.inr ⟨a, xs ++ b, by simp, Or.inl ⟨ha, xs, b, rfl, hb,
      Or.inr (elementsB_complete hx k (by omega))⟩⟩
  | .emptyObject (a := a) (b := b) ha hb, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    simp only [valueB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm]
    exact Or.inr ⟨a, b, rfl, Or.inr ⟨ha, [], b, rfl, hb, Or.inl rfl⟩⟩
  | .object (a := a) (ms := ms) (b := b) ha hm hb, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    have h1 := structural_length ha; have h2 := structural_length hb
    simp only [List.length_append] at hn
    simp only [valueB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm]
    exact Or.inr ⟨a, ms ++ b, by simp, Or.inr ⟨ha, ms, b, rfl, hb,
      Or.inr (membersB_complete hm k (by omega))⟩⟩

theorem elementsB_complete {w : List UInt8} :
    Elements p N w → ∀ n, 2 * w.length + 2 ≤ n → elementsB p N n w = true
  | .one hv, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    simp [elementsB, valueB_complete hv k (by omega)]
  | .cons (v := v) (s := s) (vs := vs) hv hs hx, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    have h2 := structural_length hs
    simp only [List.length_append] at hn
    simp only [elementsB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm]
    exact Or.inr ⟨v, s ++ vs, by simp, valueB_complete hv k (by omega), s, vs, rfl, hs,
      elementsB_complete hx k (by omega)⟩

theorem membersB_complete {w : List UInt8} :
    Members p N w → ∀ n, 2 * w.length + 2 ≤ n → membersB p N n w = true
  | .one (k := key) (c := c) (v := v) hk hc hv, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    simp only [List.length_append] at hn
    simp only [membersB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm]
    exact ⟨key ++ c ++ v, [], by simp, ⟨key, c ++ v, by simp, hk, c, v, rfl, hc,
      valueB_complete hv k (by omega)⟩, Or.inl rfl⟩
  | .cons (k := key) (c := c) (v := v) (s := s) (ms := ms) hk hc hv hs hm, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    have h1 := string_length hk; have h2 := structural_length hs
    simp only [List.length_append] at hn
    simp only [membersB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm]
    exact ⟨key ++ c ++ v, s ++ ms, by simp, ⟨key, c ++ v, by simp, hk, c, v, rfl, hc,
      valueB_complete hv k (by omega)⟩, Or.inr ⟨s, ms, rfl, hs, membersB_complete hm k (by omega)⟩⟩

end

theorem textB_iff {w : List UInt8} : textB p N w = true ↔ w ∈ language p N := by
  simp only [textB, Bool.and_eq_true, any_splits, rm]
  constructor
  · rintro ⟨a, r, rfl, ha, v, b, rfl, hb, hv⟩
    exact ⟨a, v, b, ha, valueB_sound hv, hb, by simp⟩
  · rintro ⟨a, v, b, ha, hv, hb, rfl⟩
    exact ⟨a, v ++ b, by simp, ha, v, b, rfl, hb, valueB_complete hv _ le_rfl⟩

end Silmaril.Proofs.Formats.JsonNumbers.Decide

end
