module

public import Silmaril.Formats.SExp.Scheme.Defs
import Silmaril.Proofs.Formats.SExp.Lexical.Basic

/-! # Proofs: the R7RS character classes satisfy the Scheme-family laws -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Scheme

open Silmaril.Formats Silmaril.Formats.SExpLexical Silmaril.Formats.SchemeFamily
open Silmaril.Formats.Scheme Silmaril.Proofs.Formats.SExp.Lexical

theorem laws : dialect.Laws where
  opener_paren := rfl
  delim_opener c k h := by
    simp only [dialect] at h; split at h
    · rename_i hc; subst hc; rfl
    · cases h
  delim_closer c k h := by
    simp only [dialect] at h; split at h
    · rename_i hc; subst hc; rfl
    · cases h
  closer_closeChar _ := rfl
  opener_closeChar _ := rfl
  delim_closeChar _ := rfl
  closeChar_special k := by cases k; decide
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
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact absurd hc (by decide)
  string_backslash := rfl
  string_quote := rfl
  bar w rest _ := readQuoted_escape (q := '|') (esc := escape) rfl rfl (by decide) w rest
  bar_writable _ _ _ _ := rfl
  bare_writable _ _ := rfl
  quote_writable _ _ := rfl

end Silmaril.Proofs.Formats.SExp.Scheme
