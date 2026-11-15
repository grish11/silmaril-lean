module

public import Silmaril.Formats.JsonBytes.Defs
public import Silmaril.Formats.Utf8.Thms

/-! # Proofs: the language of JSON texts over bytes (`Silmaril.Formats.JsonBytes.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonBytes

open RegularExpression Silmaril.Formats.Utf8 Silmaril.Formats.JsonBytes
open scoped Computability

/-! ## Whitespace and structural tokens -/

theorem mem_wsByte {w : List UInt8} : w ∈ wsByte.matches' ↔ ∃ b, w = [b] ∧ IsWsByte b := by
  rw [wsByte, mem_anyOf]
  simp only [List.mem_cons, List.not_mem_nil, or_false, IsWsByte]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, rfl, hb⟩
  · rintro ⟨b, rfl, hb⟩; exact ⟨b, hb, rfl⟩

theorem mem_ws {w : List UInt8} : w ∈ ws.matches' ↔ ∀ b ∈ w, IsWsByte b := by
  rw [ws, matches', Language.mem_kstar]
  constructor
  · rintro ⟨L, rfl, hL⟩ b hb
    obtain ⟨y, hy, hby⟩ := List.mem_flatten.mp hb
    obtain ⟨c, rfl, hc⟩ := mem_wsByte.mp (hL y hy)
    simp only [List.mem_singleton] at hby
    exact hby ▸ hc
  · intro h
    refine ⟨w.map ([·]), ?_, ?_⟩
    · clear h
      induction w with
      | nil => rfl
      | cons a w ih => rw [List.map_cons, List.flatten_cons, ← ih]; rfl
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
      exact mem_wsByte.mpr ⟨b, rfl, h b hb⟩

theorem nil_mem_ws : [] ∈ ws.matches' := mem_ws.mpr (by simp)

/-- A structural token starts with whitespace or with its character. -/
theorem head_structural {c : UInt8} {w : List UInt8} (h : w ∈ (structural c).matches') :
    ∃ b t, w = b :: t ∧ (IsWsByte b ∨ b = c) := by
  rw [structural, ← comp_def, ← comp_def, matches', matches', Language.mem_mul] at h
  obtain ⟨x, hx, y, -, rfl⟩ := h
  rw [Language.mem_mul] at hx
  obtain ⟨a, ha, d, hd, rfl⟩ := hx
  simp only [matches'] at hd
  change d = [c] at hd
  subst hd
  cases a with
  | nil => exact ⟨c, y, rfl, Or.inr rfl⟩
  | cons b t => exact ⟨b, t ++ [c] ++ y, by simp, Or.inl (mem_ws.mp ha b (by simp))⟩

theorem head_append {a x : List UInt8} {b : UInt8} {t : List UInt8}
    (h : a ++ x = b :: t) {c : UInt8} {s : List UInt8} (ha : a = c :: s) : c = b := by
  subst ha
  simp only [List.cons_append, List.cons.injEq] at h
  exact h.1

/-- A value whose first byte is not whitespace, `[` or `{` is a scalar. -/
theorem value_scalar_of_head {p : Profile} {b : UInt8} {t : List UInt8}
    (h : Value p (b :: t)) (hw : ¬ IsWsByte b) (ha : b ≠ 0x5B) (ho : b ≠ 0x7B) :
    (b :: t) ∈ (scalar p).matches' := by
  generalize hv : b :: t = v at h
  cases h with
  | scalar hs => exact hs
  | emptyArray hA _ | array hA _ _ =>
    obtain ⟨c, s, rfl, hc⟩ := head_structural hA
    have := head_append (by simpa using hv.symm) rfl
    subst this
    rcases hc with hc | hc
    exacts [(hw hc).elim, (ha hc).elim]
  | emptyObject hA _ | object hA _ _ =>
    obtain ⟨c, s, rfl, hc⟩ := head_structural hA
    have := head_append (by simpa using hv.symm) rfl
    subst this
    rcases hc with hc | hc
    exacts [(hw hc).elim, (ho hc).elim]

/-- The decision theorem for texts that do not start with whitespace, `[` or `{`. -/
theorem mem_language_iff_of_head {p : Profile} {b : UInt8} {t : List UInt8}
    (hw : ¬ IsWsByte b) (ha : b ≠ 0x5B) (ho : b ≠ 0x7B) :
    (b :: t) ∈ language p ↔ (b :: t) ∈ (scalar p * ws).matches' := by
  constructor
  · rintro ⟨a, v, c, hA, hV, hC, he⟩
    cases a with
    | cons x s =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd (he.1 ▸ mem_ws.mp hA x (by simp)) hw
    | nil =>
      simp only [List.nil_append] at he
      cases v with
      | nil =>
        simp only [List.nil_append] at he
        exact absurd (mem_ws.mp hC b (by simp [← he])) hw
      | cons y s =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rw [← comp_def, matches']
        exact Language.append_mem_mul (value_scalar_of_head hV hw ha ho) hC
  · intro h
    rw [← comp_def, matches', Language.mem_mul] at h
    obtain ⟨v, hv, c, hc, he⟩ := h
    exact ⟨[], v, c, nil_mem_ws, .scalar hv, hc, by simp [he]⟩

/-! ## Every JSON text is well-formed UTF-8 -/

/-- Every word of the expression is well-formed UTF-8. -/
def Good (r : RegularExpression UInt8) : Prop := ∀ w ∈ r.matches', IsWellFormed w

theorem good_mul {r s : RegularExpression UInt8} (hr : Good r) (hs : Good s) : Good (r * s) := by
  intro w hw
  rw [← comp_def, matches', Language.mem_mul] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := hw
  exact isWellFormed_append (hr a ha) (hs b hb)

theorem good_add {r s : RegularExpression UInt8} (hr : Good r) (hs : Good s) : Good (r + s) := by
  intro w hw
  rw [← plus_def, matches', Language.mem_add] at hw
  rcases hw with hw | hw
  exacts [hr w hw, hs w hw]

theorem good_one : Good 1 := by
  intro w hw
  rw [← one_def, matches', Language.mem_one] at hw
  exact hw ▸ isWellFormed_nil

theorem good_star {r : RegularExpression UInt8} (hr : Good r) : Good (star r) := by
  intro w hw
  rw [matches', Language.mem_kstar] at hw
  obtain ⟨L, rfl, hL⟩ := hw
  induction L with
  | nil => exact isWellFormed_nil
  | cons y L ih =>
    rw [List.flatten_cons]
    exact isWellFormed_append (hr y (hL y (by simp))) (ih fun z hz => hL z (by simp [hz]))

theorem good_anyOf {l : List UInt8} (h : ∀ b ∈ l, b < 0x80) : Good (anyOf l) := by
  intro w hw
  obtain ⟨b, hb, rfl⟩ := mem_anyOf.mp hw
  exact isWellFormed_of_ascii (by simpa using h b hb)

theorem good_char {b : UInt8} (h : b < 0x80) : Good (char b) := by
  intro w hw
  change w = [b] at hw
  exact isWellFormed_of_ascii (by simp [hw, h])

theorem good_byteRange {lo hi : UInt8} (h : hi < 0x80) : Good (byteRange lo hi) := by
  intro w hw
  obtain ⟨b, rfl, -, hb⟩ := mem_byteRange.mp hw
  refine isWellFormed_of_ascii ?_
  simp only [List.mem_singleton, forall_eq]
  rw [UInt8.lt_iff_toNat_lt] at h ⊢; rw [UInt8.le_iff_toNat_le] at hb; omega

theorem good_word {l : List UInt8} (h : ∀ b ∈ l, b < 0x80) : Good (word l) := by
  intro w hw
  rw [mem_word.mp hw]
  exact isWellFormed_of_ascii h

theorem good_multibyte : Good multibyte := by
  intro w hw
  refine scalar_isWellFormed ?_
  rw [Formats.Utf8.scalar, ← plus_def, matches', Language.mem_add]
  exact Or.inr hw

theorem good_ws : Good ws := good_star (good_anyOf (by decide))

theorem good_structural {c : UInt8} (h : c < 0x80) : Good (structural c) :=
  good_mul (good_mul good_ws (good_char h)) good_ws

theorem good_hexdig : Good hexdig :=
  good_add (good_add (good_byteRange (by decide)) (good_byteRange (by decide)))
    (good_byteRange (by decide))

theorem good_digits : Good digits :=
  good_mul (good_byteRange (by decide)) (good_star (good_byteRange (by decide)))

theorem good_number : Good number := by
  refine good_mul (good_mul (good_mul (good_add good_one (good_char (by decide))) ?_)
    (good_add good_one (good_mul (good_char (by decide)) good_digits)))
    (good_add good_one (good_mul (good_mul (good_anyOf (by decide))
      (good_add good_one (good_anyOf (by decide)))) good_digits))
  exact good_add (good_char (by decide))
    (good_mul (good_byteRange (by decide)) (good_star (good_byteRange (by decide))))

theorem good_uPrefix : Good uPrefix := good_mul (good_char (by decide)) (good_char (by decide))

theorem good_unescaped : Good unescaped :=
  good_add (good_add (good_add (good_byteRange (by decide)) (good_byteRange (by decide)))
    (good_byteRange (by decide))) good_multibyte

theorem good_shortEscape : Good shortEscape := good_mul (good_char (by decide)) (good_anyOf (by decide))

theorem good_surrogateEscape {l : List UInt8} (h : ∀ b ∈ l, b < 0x80) :
    Good (uPrefix * hexD * anyOf l * hexdig * hexdig) :=
  good_mul (good_mul (good_mul (good_mul good_uPrefix (good_anyOf (by decide))) (good_anyOf h))
    good_hexdig) good_hexdig

theorem good_strChar (p : Profile) : Good (strChar p) := by
  cases p with
  | rfc8259 =>
    exact good_add (good_add good_unescaped good_shortEscape)
      (good_mul (good_mul (good_mul (good_mul good_uPrefix good_hexdig) good_hexdig) good_hexdig)
        good_hexdig)
  | scalarEscapes =>
    refine good_add (good_add (good_add good_unescaped good_shortEscape) ?_)
      (good_mul (good_surrogateEscape (by decide)) (good_surrogateEscape (by decide)))
    exact good_mul good_uPrefix (good_add
      (good_mul (good_mul (good_mul (good_add (good_byteRange (by decide)) (good_anyOf (by decide)))
        good_hexdig) good_hexdig) good_hexdig)
      (good_mul (good_mul (good_mul (good_anyOf (by decide)) (good_byteRange (by decide)))
        good_hexdig) good_hexdig))

theorem good_string (p : Profile) : Good (string p) :=
  good_mul (good_mul (good_char (by decide)) (good_star (good_strChar p))) (good_char (by decide))

theorem good_scalar (p : Profile) : Good (scalar p) :=
  good_add (good_add (good_add (good_add (good_word (by decide)) (good_word (by decide)))
    (good_word (by decide))) good_number) (good_string p)

mutual

theorem value_isWellFormed {p : Profile} {w : List UInt8} : Value p w → IsWellFormed w
  | .scalar h => good_scalar p _ h
  | .emptyArray ha hb =>
    isWellFormed_append (good_structural (by decide) _ ha) (good_structural (by decide) _ hb)
  | .array ha hx hb =>
    isWellFormed_append (isWellFormed_append (good_structural (by decide) _ ha)
      (elements_isWellFormed hx)) (good_structural (by decide) _ hb)
  | .emptyObject ha hb =>
    isWellFormed_append (good_structural (by decide) _ ha) (good_structural (by decide) _ hb)
  | .object ha hm hb =>
    isWellFormed_append (isWellFormed_append (good_structural (by decide) _ ha)
      (members_isWellFormed hm)) (good_structural (by decide) _ hb)

theorem elements_isWellFormed {p : Profile} {w : List UInt8} : Elements p w → IsWellFormed w
  | .one hv => value_isWellFormed hv
  | .cons hv hs hx =>
    isWellFormed_append (isWellFormed_append (value_isWellFormed hv)
      (good_structural (by decide) _ hs)) (elements_isWellFormed hx)

theorem members_isWellFormed {p : Profile} {w : List UInt8} : Members p w → IsWellFormed w
  | .one hk hc hv =>
    isWellFormed_append (isWellFormed_append (good_string p _ hk)
      (good_structural (by decide) _ hc)) (value_isWellFormed hv)
  | .cons hk hc hv hs hm =>
    isWellFormed_append (isWellFormed_append (isWellFormed_append (isWellFormed_append
      (good_string p _ hk) (good_structural (by decide) _ hc)) (value_isWellFormed hv))
      (good_structural (by decide) _ hs)) (members_isWellFormed hm)

end

theorem language_isWellFormed {p : Profile} {w : List UInt8} (h : w ∈ language p) :
    IsWellFormed w := by
  obtain ⟨a, v, b, ha, hv, hb, rfl⟩ := h
  exact isWellFormed_append (isWellFormed_append (good_ws a ha) (value_isWellFormed hv))
    (good_ws b hb)

/-! ## The empty input -/

theorem nil_not_mem_scalar (p : Profile) : [] ∉ (scalar p).matches' := by
  rw [← rmatch_iff_matches']
  cases p <;> decide

theorem value_ne_nil {p : Profile} {w : List UInt8} (h : Value p w) : w ≠ [] := by
  rintro rfl
  generalize hv : ([] : List UInt8) = v at h
  cases h with
  | scalar hs => exact nil_not_mem_scalar p (hv ▸ hs)
  | emptyArray hA _ | array hA _ _ | emptyObject hA _ | object hA _ _ =>
    obtain ⟨c, s, rfl, -⟩ := head_structural hA
    simp at hv

theorem nil_not_mem_language (p : Profile) : [] ∉ language p := by
  rintro ⟨a, v, c, -, hV, -, he⟩
  exact value_ne_nil hV (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp he.symm).1).2

end Silmaril.Proofs.Formats.JsonBytes

end
