module

public import Silmaril.Formats.SExp.SchemeFamily.Defs
import Silmaril.Proofs.Formats.SExp.Lexical.Basic

/-! # Proofs: Scheme-family lexing lemmas -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.SchemeFamily

open Silmaril.Formats Silmaril.Formats.SExpReader Silmaril.Formats.SExpLexical
open Silmaril.Formats.SchemeFamily Silmaril.Formats.SchemeFamily.Dialect
open Silmaril.Proofs.Formats.SExp.Lexical

variable {C : Type} {D : Dialect C}

/-! ## Atmosphere -/

theorem skip_ws {c : Char} (h : isWhitespace c = true) (s : List Char) :
    skip .code (c :: s) = skip .code s := by
  simp [skip, h]

theorem skip_stop {c : Char} (r : List Char) (hw : isWhitespace c = false) (hs : c ≠ ';')
    (hh : c ≠ '#') : skip .code (c :: r) = some (c :: r) := by
  simp [skip, hw, hs, hh]

theorem skip_hash {d : Char} (r : List Char) (hd : d ≠ '|') :
    skip .code ('#' :: d :: r) = some ('#' :: d :: r) := by
  simp [skip, isWhitespace, hd]

theorem step_of_skip {s : List Char} {c : Char} {r : List Char}
    (h : skip .code s = some (c :: r)) : D.step s = D.dispatch c r := by
  simp [Dialect.step, h]

/-! ## Character classes -/

theorem not_whitespace_of_bareChar (hL : D.Laws) {c : Char} (h : D.bareChar c = true) :
    isWhitespace c = false := by
  cases hw : isWhitespace c
  · rfl
  · have := hL.delim_space c hw
    simp [Dialect.bareChar, this] at h

theorem not_delim_of_bareChar {c : Char} (h : D.bareChar c = true) : D.isDelimiter c = false := by
  simp only [Dialect.bareChar, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1.1

theorem ne_of_bareChar {c : Char} (h : D.bareChar c = true) : c ≠ '|' ∧ c ≠ '\\' := by
  simp only [Dialect.bareChar, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.2, h.2⟩

theorem ne_delim {c x : Char} (hc : D.isDelimiter c = false) (hx : D.isDelimiter x = true) :
    c ≠ x := by
  rintro rfl; rw [hc] at hx; cases hx

theorem opener_none (hL : D.Laws) {c : Char} (hc : D.isDelimiter c = false) :
    D.brackets.opener c = none := by
  cases h : D.brackets.opener c with
  | none => rfl
  | some k => have := hL.delim_opener c k h; rw [hc] at this; cases this

theorem closer_none (hL : D.Laws) {c : Char} (hc : D.isDelimiter c = false) :
    D.brackets.closer c = none := by
  cases h : D.brackets.closer c with
  | none => rfl
  | some k => have := hL.delim_closer c k h; rw [hc] at this; cases this

theorem bareChar_of_notDelim (hL : D.Laws) {c : Char}
    (h : c.isDigit = true ∨ c = '-' ∨ c = 'e' ∨ c = '/' ∨ c = '.' ∨ c = 't' ∨ c = 'f') :
    D.bareChar c = true := by
  have hd := hL.notDelim c h
  have h1 : c ≠ '|' := by rcases h with h | rfl | rfl | rfl | rfl | rfl | rfl <;> try decide
                          rintro rfl; simp [Char.isDigit] at h
  have h2 : c ≠ '\\' := by rcases h with h | rfl | rfl | rfl | rfl | rfl | rfl <;> try decide
                           rintro rfl; simp [Char.isDigit] at h
  simp [Dialect.bareChar, hd, h1, h2]

/-- A dispatch on a first character that starts a bare token. -/
theorem dispatch_bare (hL : D.Laws) {c : Char} (r : List Char) (hb : D.bareChar c = true)
    (h1 : c ≠ '\'') (h2 : c ≠ '`') (h3 : c ≠ ',') (h4 : c ≠ '#') :
    D.dispatch c r = D.bare (c :: r) := by
  have hd := not_delim_of_bareChar hb
  have hq : c ≠ '"' := ne_delim hd hL.delim_special.2
  have hbar := (ne_of_bareChar hb).1
  simp [Dialect.dispatch, opener_none hL hd, closer_none hL hd, hq, hbar, h1, h2, h3, h4]

/-! ## What follows a printed atom -/

/-- After a printed atom: the end, or a delimiter that is not `|` or `\`. -/
def Delimited (D : Dialect C) (rest : List Char) : Prop :=
  ∀ c r, rest = c :: r → D.isDelimiter c = true ∧ c ≠ '|' ∧ c ≠ '\\' ∧ c ≠ '#'

theorem delimited_of_follows (hL : D.Laws) {rest : List Char} (h : Follows D.text rest) :
    Delimited D rest := by
  rintro c r rfl
  rcases h with h | ⟨r', h⟩ | ⟨k, r', h⟩
  · cases h
  · cases h
    exact ⟨hL.delim_space ' ' (by decide), by decide, by decide, by decide⟩
  · simp only [Dialect.text, List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, h2, -, h4, -⟩ := hL.closeChar_special k
    exact ⟨hL.delim_closeChar k, h1, h2, h4⟩

theorem not_bareChar_of_delimited {rest : List Char} (h : Delimited D rest) :
    ∀ c r, rest = c :: r → D.bareChar c = false := by
  intro c r hr
  have := (h c r hr).1
  simp [Dialect.bareChar, this]

theorem bare_append {w rest : List Char} (hw : ∀ x ∈ w, D.bareChar x = true)
    (hne : w ≠ []) (hrest : Delimited D rest) (hdot : w ≠ ['.']) :
    D.bare (w ++ rest) =
      match D.classify w with
      | some a => .token (.atom a) rest
      | none => .error := by
  have ht := takeToken_append hw (not_bareChar_of_delimited hrest)
  have hhead : (rest.head? = some '|' || rest.head? = some '\\') = false := by
    cases rest with
    | nil => rfl
    | cons c r =>
        obtain ⟨-, h1, h2, -⟩ := hrest c r rfl
        simp [h1, h2]
  simp only [Dialect.bare, ht, hne, hdot, ite_false, hhead]
  rfl

/-! ## Numerals -/

theorem digits?_none {cs : List Char} {x : Char} (hx : x ∈ cs) (hd : x.isDigit = false) :
    digits? cs = none := by
  have : cs.all Char.isDigit = false := by
    rw [List.all_eq_false]; exact ⟨x, hx, by simp [hd]⟩
  simp [digits?, this]

/-- Numerals start with a digit, or a minus sign and a digit. -/
def NumHead (w : List Char) : Prop :=
  ∃ c r, w = c :: r ∧ (c.isDigit = true ∨ (c = '-' ∧ ∃ d r', r = d :: r' ∧ d.isDigit = true))

theorem numHead_natText_append (n : Nat) (w : List Char) : NumHead (natText n ++ w) := by
  obtain ⟨c, r, h, hc⟩ := natText_head n
  exact ⟨c, r ++ w, by simp [h], Or.inl hc⟩

theorem numHead_intText_append (n : Int) (w : List Char) : NumHead (intText n ++ w) := by
  unfold intText
  split
  · obtain ⟨c, r, h, hc⟩ := natText_head n.natAbs
    exact ⟨'-', _, rfl, Or.inr ⟨rfl, c, r ++ w, by simp [h], hc⟩⟩
  · exact numHead_natText_append _ w

theorem numHead_ratText (q : ℚ) : NumHead (ratText q) := by
  unfold ratText
  split
  · simpa using numHead_intText_append q.num []
  · exact numHead_intText_append q.num _

theorem numHead_decText (d : Decimal) : NumHead (Decimal.text 'e' d) := by
  unfold Decimal.text
  cases d.negative
  · simpa using numHead_natText_append d.significand ('e' :: intText d.exponent)
  · obtain ⟨c, r, h, hc⟩ := natText_head d.significand
    exact ⟨'-', _, rfl, Or.inr ⟨rfl, c, r ++ 'e' :: intText d.exponent, by simp [h], hc⟩⟩

theorem numericLooking_of_numHead {w : List Char} (h : NumHead w) : numericLooking w = true := by
  obtain ⟨c, r, rfl, h⟩ := h
  rcases h with hc | ⟨rfl, d, r', rfl, hd⟩
  · cases r with
    | nil => simp [numericLooking, hc]
    | cons d r => simp [numericLooking, hc]
  · simp [numericLooking, hd]

theorem ne_dot_of_numHead {w : List Char} (h : NumHead w) : w ≠ ['.'] := by
  obtain ⟨c, r, rfl, h⟩ := h
  rcases h with hc | ⟨rfl, -⟩
  · rintro ⟨⟩; simp [Char.isDigit] at hc
  · simp

theorem ratText_chars (q : ℚ) : ∀ x ∈ ratText q,
    x.isDigit = true ∨ x = '-' ∨ x = '/' := by
  intro x hx
  unfold ratText at hx
  split at hx
  · rcases intText_chars _ x hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · rcases intText_chars _ x hx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl (natText_isDigit _ x hx)

theorem decText_chars (d : Decimal) : ∀ x ∈ Decimal.text 'e' d,
    x.isDigit = true ∨ x = '-' ∨ x = 'e' := by
  intro x hx
  unfold Decimal.text at hx
  simp only [List.mem_append, List.mem_cons] at hx
  rcases hx with (hx | hx) | rfl | hx
  · split at hx <;> simp_all
  · exact Or.inl (natText_isDigit _ x hx)
  · exact Or.inr (Or.inr rfl)
  · rcases intText_chars _ x hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem rational?_decText (d : Decimal) : rational? (Decimal.text 'e' d) = none := by
  have hslash : ∀ x ∈ Decimal.text 'e' d, (x != '/') = true := by
    intro x hx
    rcases decText_chars d x hx with h | rfl | rfl
    · have : x ≠ '/' := by rintro rfl; simp [Char.isDigit] at h
      simpa using this
    · decide
    · decide
  have hmem : 'e' ∈ Decimal.text 'e' d := by simp [Decimal.text]
  unfold rational?
  rw [show Decimal.text 'e' d = Decimal.text 'e' d ++ [] by simp,
    takeToken_append hslash (by simp)]
  obtain ⟨c, r, hcr, hh⟩ := numHead_decText d
  rw [hcr] at hmem ⊢
  rcases hh with hc | ⟨rfl, -⟩
  · have hs := not_sign_of_isDigit hc
    simp only [int?, hs.1, hs.2, ite_false]
    rw [digits?_none hmem (by decide)]
    rfl
  · simp only [int?, ite_true]
    have : 'e' ∈ r := by simpa using hmem
    rw [digits?_none this (by decide)]
    rfl

theorem classify_ratText (q : ℚ) : D.classify (ratText q) = some (.exact q) := by
  simp [Dialect.classify, numericLooking_of_numHead (numHead_ratText q), rational?_ratText]

theorem classify_decText (d : Decimal) : D.classify (Decimal.text 'e' d) = some (.inexact d) := by
  have hr := readDecimal_text (isMarker := isExponent) (m := 'e') (by decide) (by decide)
    (by decide) d
  simp [Dialect.classify, numericLooking_of_numHead (numHead_decText d), rational?_decText, hr]

end Silmaril.Proofs.Formats.SExp.SchemeFamily
