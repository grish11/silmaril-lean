module

public import Silmaril.Logic.Smt.Uflia.SExpr.Defs
public import Silmaril.Logic.Smt.SExpr.Reader.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming
open Silmaril.Logic.Smt.SExpr.Writer

private def Initial (c : Char) : Bool :=
  c.isAlpha || "~!@$%^&*_-+=<>.?/".toList.contains c

private theorem initial_legal (c : Char) (hc : Initial c = true) : LegalChar c := by
  simp only [Initial, Bool.or_eq_true] at hc
  rcases hc with halpha | hpunct
  · have hbounds : (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨
        (97 ≤ c.toNat ∧ c.toNat ≤ 122) := by
      simpa [Char.isAlpha, Char.isUpper, Char.isLower, UInt32.le_iff_toNat_le] using halpha
    unfold LegalChar
    omega
  · have hchars : c = '~' ∨ c = '!' ∨ c = '@' ∨ c = '$' ∨ c = '%' ∨ c = '^' ∨ c = '&' ∨ c = '*' ∨ c = '_' ∨ c = '-' ∨ c = '+' ∨ c = '=' ∨ c = '<' ∨ c = '>' ∨ c = '.' ∨ c = '?' ∨ c = '/' := by
      simpa using hpunct
    rcases hchars with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals unfold LegalChar; decide

private theorem digit_legal (c : Char) (hc : c.isDigit = true) : LegalChar c := by
  have hbounds : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := Char.isDigit_iff_toNat.mp hc
  unfold LegalChar
  omega

/-- Every admitted simple symbol is an actual nonempty lexer-safe ASCII atom.
This follows from the pinned ASCII character predicates, not a parser oracle. -/
theorem simpleSymbol_legalAtom (name : String) (h : simpleSymbol name = true) : LegalAtom name := by
  cases hchars : name.toList with
  | nil => simp [simpleSymbol, hchars] at h
  | cons c cs =>
    simp only [simpleSymbol, hchars, Bool.and_eq_true] at h
    obtain ⟨⟨hi, htail⟩, _⟩ := h
    constructor
    · simp [hchars]
    · intro d hd
      rw [hchars] at hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact initial_legal d hi
      · have hchar := List.all_eq_true.mp htail d hd
        change (Initial d || d.isDigit) = true at hchar
        cases hi' : Initial d with
        | true => exact initial_legal d hi'
        | false =>
          have hdigit : d.isDigit = true := by simpa only [hi', Bool.false_or] using hchar
          exact digit_legal d hdigit

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming
