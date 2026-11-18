module

public import Silmaril.Formats.SExp.Racket.Defs
import Silmaril.Proofs.Formats.SExp.Lexical.Basic

/-! # Proofs: Racket's character classes satisfy the Scheme-family laws -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Racket

open Silmaril.Formats Silmaril.Formats.SExpLexical Silmaril.Formats.SchemeFamily
open Silmaril.Formats.Racket Silmaril.Proofs.Formats.SExp.Lexical

theorem laws : dialect.Laws where
  opener_paren := rfl
  delim_opener c k h := by
    simp only [dialect, opener] at h
    split at h
    · rename_i hc; subst hc; rfl
    split at h
    · rename_i hc; subst hc; rfl
    split at h
    · rename_i hc; subst hc; rfl
    · cases h
  delim_closer c k h := by
    simp only [dialect, closer] at h
    split at h
    · rename_i hc; subst hc; rfl
    split at h
    · rename_i hc; subst hc; rfl
    split at h
    · rename_i hc; subst hc; rfl
    · cases h
  closer_closeChar k := by cases k <;> rfl
  opener_closeChar k := by cases k <;> rfl
  delim_closeChar k := by cases k <;> rfl
  closeChar_special k := by cases k <;> decide
  opener_special := by decide
  closer_special := by decide
  delim_space c h := by simp [dialect, isDelimiter, h]
  delim_special := by decide
  notDelim c hc := by
    change isDelimiter c = false
    cases hd : isDelimiter c
    · rfl
    · exfalso
      simp only [isDelimiter, Dialect.isWhitespace, Bool.or_eq_true, decide_eq_true_eq,
        or_assoc] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> exact absurd hc (by decide)
  string_backslash := rfl
  string_quote := rfl
  bar w rest h := by
    simp [dialect] at h
    show readQuoted '|' (fun _ => none) _ = _
    rw [escapeQuoted_clean h.1 h.2]
    exact readQuoted_clean rest h.1 h.2
  bar_writable cs w rest h := by
    obtain ⟨h1, h2⟩ := readQuoted_noEscape h
    simp [dialect, h1, h2]
  bare_writable w h := by
    have : ∀ x ∈ w, x ≠ '|' ∧ x ≠ '\\' := by
      intro x hx
      have := List.all_eq_true.1 h x hx
      simp only [Dialect.bareChar, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
      exact ⟨this.1.2, this.2⟩
    have h1 : '|' ∉ w := fun hm => (this _ hm).1 rfl
    have h2 : '\\' ∉ w := fun hm => (this _ hm).2 rfl
    simp [dialect, h1, h2]
  quote_writable s hs := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Silmaril.Proofs.Formats.SExp.Racket
