module

public import Silmaril.Formats.JsonBytes.Depth.Defs
import Silmaril.Proofs.Formats.JsonBytes.Basic
import Silmaril.Proofs.Formats.JsonBytes.Decide

/-! # Proofs: JSON texts of bounded nesting depth (`Silmaril.Formats.JsonBytes.Depth.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonBytes.Depth

open RegularExpression Silmaril.Formats.JsonBytes Silmaril.Formats.JsonBytes.Decide
open Silmaril.Proofs.Formats.JsonBytes.Decide (any_splits rm structural_length string_length
  value_length succ_of_le)

/-! ## Forgetting the depth -/

mutual

theorem ValueAt.toValue {p : Profile} {d : Nat} {w : List UInt8} : ValueAt p d w → Value p w
  | .scalar h => .scalar h
  | .emptyArray ha hb => .emptyArray ha hb
  | .array ha hx hb => .array ha (ElementsAt.toElements hx) hb
  | .emptyObject ha hb => .emptyObject ha hb
  | .object ha hm hb => .object ha (MembersAt.toMembers hm) hb

theorem ElementsAt.toElements {p : Profile} {d : Nat} {w : List UInt8} :
    ElementsAt p d w → Elements p w
  | .one hv => .one (ValueAt.toValue hv)
  | .cons hv hs hx => .cons (ValueAt.toValue hv) hs (ElementsAt.toElements hx)

theorem MembersAt.toMembers {p : Profile} {d : Nat} {w : List UInt8} :
    MembersAt p d w → Members p w
  | .one hk hc hv => .one hk hc (ValueAt.toValue hv)
  | .cons hk hc hv hs hm => .cons hk hc (ValueAt.toValue hv) hs (MembersAt.toMembers hm)

end

/-! ## Monotonicity in the depth -/

mutual

theorem ValueAt.mono {p : Profile} {d e : Nat} {w : List UInt8} :
    ValueAt p d w → d ≤ e → ValueAt p e w
  | .scalar h, _ => .scalar h
  | .emptyArray (d := d) ha hb, h => by
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    exact .emptyArray ha hb
  | .array (d := d) ha hx hb, h => by
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    exact .array ha (ElementsAt.mono hx (by omega)) hb
  | .emptyObject (d := d) ha hb, h => by
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    exact .emptyObject ha hb
  | .object (d := d) ha hm hb, h => by
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    exact .object ha (MembersAt.mono hm (by omega)) hb

theorem ElementsAt.mono {p : Profile} {d e : Nat} {w : List UInt8} :
    ElementsAt p d w → d ≤ e → ElementsAt p e w
  | .one hv, h => .one (ValueAt.mono hv h)
  | .cons hv hs hx, h => .cons (ValueAt.mono hv h) hs (ElementsAt.mono hx h)

theorem MembersAt.mono {p : Profile} {d e : Nat} {w : List UInt8} :
    MembersAt p d w → d ≤ e → MembersAt p e w
  | .one hk hc hv, h => .one hk hc (ValueAt.mono hv h)
  | .cons hk hc hv hs hm, h => .cons hk hc (ValueAt.mono hv h) hs (MembersAt.mono hm h)

end

/-! ## Every value has a depth -/

mutual

theorem Value.exists_valueAt {p : Profile} {w : List UInt8} : Value p w → ∃ d, ValueAt p d w
  | .scalar h => ⟨0, .scalar h⟩
  | .emptyArray ha hb => ⟨1, .emptyArray ha hb⟩
  | .array ha hx hb => by
    obtain ⟨d, hd⟩ := Elements.exists_elementsAt hx
    exact ⟨d + 1, .array ha hd hb⟩
  | .emptyObject ha hb => ⟨1, .emptyObject ha hb⟩
  | .object ha hm hb => by
    obtain ⟨d, hd⟩ := Members.exists_membersAt hm
    exact ⟨d + 1, .object ha hd hb⟩

theorem Elements.exists_elementsAt {p : Profile} {w : List UInt8} :
    Elements p w → ∃ d, ElementsAt p d w
  | .one hv => by
    obtain ⟨d, hd⟩ := Value.exists_valueAt hv
    exact ⟨d, .one hd⟩
  | .cons hv hs hx => by
    obtain ⟨d, hd⟩ := Value.exists_valueAt hv
    obtain ⟨e, he⟩ := Elements.exists_elementsAt hx
    exact ⟨max d e, .cons (ValueAt.mono hd (le_max_left _ _)) hs
      (ElementsAt.mono he (le_max_right _ _))⟩

theorem Members.exists_membersAt {p : Profile} {w : List UInt8} :
    Members p w → ∃ d, MembersAt p d w
  | .one hk hc hv => by
    obtain ⟨d, hd⟩ := Value.exists_valueAt hv
    exact ⟨d, .one hk hc hd⟩
  | .cons hk hc hv hs hm => by
    obtain ⟨d, hd⟩ := Value.exists_valueAt hv
    obtain ⟨e, he⟩ := Members.exists_membersAt hm
    exact ⟨max d e, .cons hk hc (ValueAt.mono hd (le_max_left _ _)) hs
      (MembersAt.mono he (le_max_right _ _))⟩

end

theorem languageAt_mono {p : Profile} {d e : Nat} (h : d ≤ e) : languageAt p d ≤ languageAt p e := by
  rintro w ⟨a, v, b, ha, hv, hb, rfl⟩
  exact ⟨a, v, b, ha, ValueAt.mono hv h, hb, rfl⟩

theorem languageAt_le_language (p : Profile) (d : Nat) : languageAt p d ≤ language p := by
  rintro w ⟨a, v, b, ha, hv, hb, rfl⟩
  exact ⟨a, v, b, ha, ValueAt.toValue hv, hb, rfl⟩

theorem iUnion_languageAt (p : Profile) :
    (⋃ d, (languageAt p d : Set (List UInt8))) = language p := by
  ext w
  constructor
  · intro h
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp h
    exact languageAt_le_language p d hd
  · rintro ⟨a, v, b, ha, hv, hb, rfl⟩
    obtain ⟨d, hd⟩ := Value.exists_valueAt hv
    exact Set.mem_iUnion.mpr ⟨d, a, v, b, ha, hd, hb, rfl⟩

/-- At depth `0` only scalars occur. -/
theorem valueAt_zero {p : Profile} {w : List UInt8} : ValueAt p 0 w ↔ w ∈ (scalar p).matches' := by
  constructor
  · intro h
    cases h with
    | scalar h => exact h
  · exact .scalar

/-! ## The decision procedure -/

mutual

theorem valueAtB_sound {p : Profile} :
    ∀ {n d : Nat} {w : List UInt8}, valueAtB p n d w = true → ValueAt p d w
  | 0, _, _, h => by simp [valueAtB] at h
  | _ + 1, 0, _, h => by
    simp only [valueAtB, rm] at h
    exact .scalar h
  | n + 1, d + 1, w, h => by
    simp only [valueAtB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm] at h
    rcases h with hs | ⟨a, r, rfl, h⟩
    · exact .scalar hs
    rcases h with ⟨ha, m, b, rfl, hb, hm⟩ | ⟨ha, m, b, rfl, hb, hm⟩
    · rcases hm with hm | hm
      · rw [List.isEmpty_iff.mp hm, List.nil_append]
        exact .emptyArray ha hb
      · rw [← List.append_assoc]
        exact .array ha (elementsAtB_sound hm) hb
    · rcases hm with hm | hm
      · rw [List.isEmpty_iff.mp hm, List.nil_append]
        exact .emptyObject ha hb
      · rw [← List.append_assoc]
        exact .object ha (membersAtB_sound hm) hb

theorem elementsAtB_sound {p : Profile} :
    ∀ {n d : Nat} {w : List UInt8}, elementsAtB p n d w = true → ElementsAt p d w
  | 0, _, _, h => by simp [elementsAtB] at h
  | n + 1, d, w, h => by
    simp only [elementsAtB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm] at h
    rcases h with hv | ⟨v, r, rfl, hv, s, vs, rfl, hs, hx⟩
    · exact .one (valueAtB_sound hv)
    · rw [← List.append_assoc]
      exact .cons (valueAtB_sound hv) hs (elementsAtB_sound hx)

theorem membersAtB_sound {p : Profile} :
    ∀ {n d : Nat} {w : List UInt8}, membersAtB p n d w = true → MembersAt p d w
  | 0, _, _, h => by simp [membersAtB] at h
  | n + 1, d, w, h => by
    simp only [membersAtB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm] at h
    obtain ⟨m, r, rfl, ⟨k, kr, rfl, hk, c, v, rfl, hc, hv⟩, hr⟩ := h
    rcases hr with hr | ⟨s, ms, rfl, hs, hm⟩
    · rw [List.isEmpty_iff.mp hr, List.append_nil, ← List.append_assoc]
      exact .one hk hc (valueAtB_sound hv)
    · simp only [← List.append_assoc]
      exact .cons hk hc (valueAtB_sound hv) hs (membersAtB_sound hm)

end

theorem valueAt_length {p : Profile} {d : Nat} {w : List UInt8} (h : ValueAt p d w) :
    1 ≤ w.length :=
  value_length (ValueAt.toValue h)

mutual

theorem valueAtB_complete {p : Profile} {d : Nat} {w : List UInt8} :
    ValueAt p d w → ∀ n, 2 * w.length + 1 ≤ n → valueAtB p n d w = true
  | .scalar (d := d) hs, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    cases d <;> simp [valueAtB, rm.mpr hs]
  | .emptyArray (a := a) (b := b) ha hb, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    simp only [valueAtB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm]
    exact Or.inr ⟨a, b, rfl, Or.inl ⟨ha, [], b, rfl, hb, Or.inl rfl⟩⟩
  | .array (a := a) (xs := xs) (b := b) ha hx hb, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    have h1 := structural_length ha; have h2 := structural_length hb
    simp only [List.length_append] at hn
    simp only [valueAtB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm]
    exact Or.inr ⟨a, xs ++ b, by simp, Or.inl ⟨ha, xs, b, rfl, hb,
      Or.inr (elementsAtB_complete hx k (by omega))⟩⟩
  | .emptyObject (a := a) (b := b) ha hb, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    simp only [valueAtB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm]
    exact Or.inr ⟨a, b, rfl, Or.inr ⟨ha, [], b, rfl, hb, Or.inl rfl⟩⟩
  | .object (a := a) (ms := ms) (b := b) ha hm hb, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    have h1 := structural_length ha; have h2 := structural_length hb
    simp only [List.length_append] at hn
    simp only [valueAtB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm]
    exact Or.inr ⟨a, ms ++ b, by simp, Or.inr ⟨ha, ms, b, rfl, hb,
      Or.inr (membersAtB_complete hm k (by omega))⟩⟩

theorem elementsAtB_complete {p : Profile} {d : Nat} {w : List UInt8} :
    ElementsAt p d w → ∀ n, 2 * w.length + 2 ≤ n → elementsAtB p n d w = true
  | .one hv, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    simp [elementsAtB, valueAtB_complete hv k (by omega)]
  | .cons (v := v) (s := s) (vs := vs) hv hs hx, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    have h1 := valueAt_length hv; have h2 := structural_length hs
    simp only [List.length_append] at hn
    simp only [elementsAtB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm]
    exact Or.inr ⟨v, s ++ vs, by simp, valueAtB_complete hv k (by omega), s, vs, rfl, hs,
      elementsAtB_complete hx k (by omega)⟩

theorem membersAtB_complete {p : Profile} {d : Nat} {w : List UInt8} :
    MembersAt p d w → ∀ n, 2 * w.length + 2 ≤ n → membersAtB p n d w = true
  | .one (k := key) (c := c) (v := v) hk hc hv, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    simp only [List.length_append] at hn
    simp only [membersAtB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm]
    exact ⟨key ++ c ++ v, [], by simp, ⟨key, c ++ v, by simp, hk, c, v, rfl, hc,
      valueAtB_complete hv k (by omega)⟩, Or.inl rfl⟩
  | .cons (k := key) (c := c) (v := v) (s := s) (ms := ms) hk hc hv hs hm, n, hn => by
    obtain ⟨k, rfl⟩ := succ_of_le hn
    have h1 := string_length hk; have h2 := structural_length hs
    simp only [List.length_append] at hn
    simp only [membersAtB, Bool.or_eq_true, Bool.and_eq_true, any_splits, rm]
    exact ⟨key ++ c ++ v, s ++ ms, by simp, ⟨key, c ++ v, by simp, hk, c, v, rfl, hc,
      valueAtB_complete hv k (by omega)⟩,
      Or.inr ⟨s, ms, rfl, hs, membersAtB_complete hm k (by omega)⟩⟩

end

theorem textAtB_iff {p : Profile} {d : Nat} {w : List UInt8} :
    textAtB p d w = true ↔ w ∈ languageAt p d := by
  simp only [textAtB, Bool.and_eq_true, any_splits, rm]
  constructor
  · rintro ⟨a, r, rfl, ha, v, b, rfl, hb, hv⟩
    exact ⟨a, v, b, ha, valueAtB_sound hv, hb, by simp⟩
  · rintro ⟨a, v, b, ha, hv, hb, rfl⟩
    exact ⟨a, v ++ b, by simp, ha, v, b, rfl, hb, valueAtB_complete hv _ le_rfl⟩

end Silmaril.Proofs.Formats.JsonBytes.Depth

end
