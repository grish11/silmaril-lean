module

public import Silmaril.Formats.SExp.Lexical.Defs
public import Mathlib.Algebra.Ring.Rat

/-! # Proofs: the shared lexical scanners invert their printers -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Lexical

open Silmaril.Formats.SExpLexical

theorem takeToken_append {p : Char → Bool} {w rest : List Char}
    (hw : ∀ c ∈ w, p c = true) (hr : ∀ c r, rest = c :: r → p c = false) :
    takeToken p (w ++ rest) = (w, rest) := by
  induction w with
  | nil =>
      cases rest with
      | nil => rfl
      | cons c r => simp [takeToken, hr c r rfl]
  | cons c w ih =>
      have hc := hw c (by simp)
      simp [takeToken, hc, ih (fun d hd => hw d (by simp [hd]))]

theorem readQuoted_escape {q : Char} {esc : Char → Option Char}
    (hb : esc '\\' = some '\\') (hq : esc q = some q) (hqb : q ≠ '\\') (w rest : List Char) :
    readQuoted q esc (escapeQuoted q w ++ q :: rest) = some (w, rest) := by
  induction w with
  | nil => simp [escapeQuoted, readQuoted]
  | cons c w ih =>
      by_cases hc : c = q ∨ c = '\\'
      · have hesc : esc c = some c := by rcases hc with rfl | rfl <;> assumption
        have hcb : (c == q || c == '\\') = true := by rcases hc with rfl | rfl <;> simp
        simp only [escapeQuoted]
        rw [ite_eq_left (by simpa using hcb)]
        have hbq : ('\\' = q) = False := by simp [Ne.symm hqb]
        simp [readQuoted, readEscape, hbq, hesc, ih]
      · simp only [not_or] at hc
        simp only [escapeQuoted]
        simp [readQuoted, hc.1, hc.2, ih]

theorem escapeQuoted_clean {q : Char} {w : List Char} (hq : q ∉ w) (hb : '\\' ∉ w) :
    escapeQuoted q w = w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
      simp only [List.mem_cons, not_or] at hq hb
      have hc : (c == q || c == '\\') = false := by simp [Ne.symm hq.1, Ne.symm hb.1]
      simp [escapeQuoted, Ne.symm hq.1, Ne.symm hb.1, ih hq.2 hb.2]

theorem readQuoted_clean {q : Char} {esc : Char → Option Char} {w : List Char}
    (rest : List Char) (hq : q ∉ w) (hb : '\\' ∉ w) :
    readQuoted q esc (w ++ q :: rest) = some (w, rest) := by
  induction w with
  | nil => simp [readQuoted]
  | cons c w ih =>
      simp only [List.mem_cons, not_or] at hq hb
      simp [readQuoted, Ne.symm hq.1, Ne.symm hb.1, ih hq.2 hb.2]

theorem readQuoted_noEscape {q : Char} : ∀ {cs w rest : List Char},
    readQuoted q (fun _ => none) cs = some (w, rest) → q ∉ w ∧ '\\' ∉ w := by
  intro cs
  induction cs with
  | nil => intro w rest h; simp [readQuoted] at h
  | cons c cs ih =>
      intro w rest h
      simp only [readQuoted] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp
      · split at h
        · cases cs <;> simp [readEscape] at h
        · rename_i hcq hcb
          cases hr : readQuoted q (fun _ => none) cs with
          | none => rw [hr] at h; cases h
          | some p =>
              obtain ⟨w', rest'⟩ := p
              rw [hr] at h
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              obtain ⟨h1, h2⟩ := ih hr
              simp only [List.mem_cons, not_or]
              exact ⟨⟨Ne.symm hcq, h1⟩, ⟨Ne.symm hcb, h2⟩⟩

theorem ofDigits_eq (cs : List Char) : ofDigits cs = Nat.ofDigitChars 10 cs 0 :=
  Nat.ofDigitChars_eq_foldl.symm

theorem natText_isDigit (n : Nat) : ∀ c ∈ natText n, c.isDigit = true :=
  fun _ hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

theorem natText_ne_nil (n : Nat) : natText n ≠ [] := Nat.toDigits_ne_nil

theorem natText_head (n : Nat) : ∃ c r, natText n = c :: r ∧ c.isDigit = true := by
  cases h : natText n with
  | nil => exact absurd h (natText_ne_nil n)
  | cons c r => exact ⟨c, r, rfl, natText_isDigit n c (by simp [h])⟩

theorem digits?_natText (n : Nat) : digits? (natText n) = some n := by
  have hall : (natText n).all Char.isDigit = true := List.all_eq_true.2 (natText_isDigit n)
  unfold digits?
  rw [ite_eq_left ⟨natText_ne_nil n, hall⟩]
  simp [natText, ofDigits_eq]

theorem not_sign_of_isDigit {c : Char} (h : c.isDigit = true) : c ≠ '-' ∧ c ≠ '+' := by
  constructor <;> rintro rfl <;> simp [Char.isDigit] at h

theorem int?_intText (n : Int) : int? (intText n) = some n := by
  unfold intText
  split
  · simp [int?, digits?_natText, Functor.map]; omega
  · obtain ⟨c, r, hcr, hd⟩ := natText_head n.toNat
    have hs := not_sign_of_isDigit hd
    rw [hcr]
    simp only [int?, hs.1, hs.2, ite_false]
    rw [← hcr, digits?_natText]
    simp [Functor.map]; omega

theorem intText_chars (n : Int) : ∀ c ∈ intText n, c.isDigit = true ∨ c = '-' := by
  intro c hc
  unfold intText at hc
  split at hc
  · simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact Or.inr rfl
    · exact Or.inl (natText_isDigit _ c hc)
  · exact Or.inl (natText_isDigit _ c hc)

theorem intText_ne_nil (n : Int) : intText n ≠ [] := by
  unfold intText; split
  · simp
  · exact natText_ne_nil _

theorem not_slash_of_intText {n : Int} : ∀ c ∈ intText n, (c != '/') = true := by
  intro c hc
  rcases intText_chars n c hc with h | rfl
  · have : c ≠ '/' := by rintro rfl; simp [Char.isDigit] at h
    simpa using this
  · decide

theorem rational?_ratText (q : ℚ) : rational? (ratText q) = some q := by
  unfold ratText
  split
  · rename_i hden
    unfold rational?
    rw [show intText q.num = intText q.num ++ [] from (List.append_nil _).symm,
      takeToken_append not_slash_of_intText (by simp)]
    simp only [int?_intText]
    simp only [Functor.map, Option.map_some]
    congr 1
    exact (Rat.den_eq_one_iff q).1 hden
  · unfold rational?
    rw [takeToken_append not_slash_of_intText (by simp)]
    simp only [int?_intText, digits?_natText, q.den_nz, ite_false]
    congr 1
    exact Rat.num_div_den q

theorem readDecimal_text {isMarker : Char → Bool} {m : Char} (hm : isMarker m = true)
    (hmd : m.isDigit = false) (hmp : m ≠ '.') (d : Decimal) :
    readDecimal isMarker (Decimal.text m d) = some (d, some m) := by
  obtain ⟨neg, sig, ex⟩ := d
  obtain ⟨c, r, hcr, hcd⟩ := natText_head sig
  have hs := not_sign_of_isDigit hcd
  have hsign : sign (Decimal.text m ⟨neg, sig, ex⟩) = (neg, natText sig ++ m :: intText ex) := by
    cases neg
    · simp only [Decimal.text, Bool.false_eq_true, ite_false, List.nil_append, hcr,
        List.cons_append, sign, hs.1, hs.2]
    · simp [Decimal.text, sign]
  have htake : takeToken Char.isDigit (natText sig ++ m :: intText ex) =
      (natText sig, m :: intText ex) :=
    takeToken_append (natText_isDigit sig) (by intro c r h; cases h; exact hmd)
  have hne : (natText sig).isEmpty = false := by
    cases h : natText sig with
    | nil => exact absurd h (natText_ne_nil _)
    | cons => rfl
  simp only [readDecimal, hsign, htake, hmp, ite_false, hne, Bool.false_and, List.append_nil,
    hm, ite_true, int?_intText]
  simp [Functor.map, natText, ofDigits_eq, Nat.ofDigitChars_ten_toDigits]

end Silmaril.Proofs.Formats.SExp.Lexical
