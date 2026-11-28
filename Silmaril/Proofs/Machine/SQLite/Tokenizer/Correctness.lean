module

public import Silmaril.Machine.SQLite.Tokenizer.Defs

public section

namespace Silmaril.Proofs.Machine.SQLite.Tokenizer

open Silmaril.Machine.SQLite.Tokenizer

private theorem word_not_space {c : Char} (h : isWordStart c = true) :
    isSpace c = false := by
  cases hc : isSpace c
  · rfl
  · simp [isSpace] at hc
    rcases hc with ((((rfl | rfl) | rfl) | rfl) | rfl) <;> contradiction

private theorem uncons_map {out : Except Error (List Token)} {head : Token} {tokens : List Token}
    (h : out.map (head :: ·) = .ok tokens) :
    ∃ tail, out = .ok tail ∧ tokens = head :: tail := by
  cases out with
  | error error => contradiction
  | ok tail => exact ⟨tail, rfl, (Except.ok.inj h).symm⟩

theorem scan_sound {input : State} {tokens : List Token}
    (h : scan input = .ok tokens) : Lexes input tokens := by
  fun_induction scan generalizing tokens
  case case1 => cases h; exact .done
  case case2 =>
    rename_i space ih
    exact .space space (ih h)
  case case3 =>
    rename_i starts _ ih
    obtain ⟨_, tail, rfl⟩ := uncons_map h
    exact .word starts (ih tail)
  case case4 =>
    rename_i ih
    obtain ⟨_, tail, rfl⟩ := uncons_map h
    exact .equals (ih tail)
  case case5 =>
    rename_i ih
    obtain ⟨_, tail, rfl⟩ := uncons_map h
    exact .parameterOne (ih tail)
  case case6 =>
    rename_i ih
    obtain ⟨_, tail, rfl⟩ := uncons_map h
    exact .semicolon (ih tail)
  case case7 => contradiction

theorem scan_complete {input : State} {tokens : List Token}
    (h : Lexes input tokens) : scan input = .ok tokens := by
  induction h with
  | done => rw [scan.eq_def]
  | space h _ ih =>
    rw [scan.eq_def]
    simpa only [h, ite_true] using ih
  | word h _ ih =>
    rw [scan.eq_def]
    simp only [word_not_space h, Bool.false_eq_true, ite_false, h, ite_true, ih]
    rfl
  | equals _ ih | parameterOne _ ih | semicolon _ ih =>
    rw [scan.eq_def]
    change (scan _).map _ = _
    rw [ih]
    rfl

theorem lexes_render {tokens : List Token} (h : ∀ token ∈ tokens, Token.Canonical token) :
    Lexes (render tokens) tokens := by
  induction tokens with
  | nil => exact .done
  | cons token tokens ih =>
    have canonical := h token (List.mem_cons_self)
    have spaced := Lexes.space (c := ' ') rfl (ih fun t ht => h t (List.mem_cons_of_mem _ ht))
    cases token with
    | equals => exact .equals spaced
    | parameterOne => exact .parameterOne spaced
    | semicolon => exact .semicolon spaced
    | word spelling =>
      change CanonicalWord spelling at canonical
      unfold CanonicalWord at canonical
      split at canonical
      · contradiction
      next c rest chars =>
        obtain ⟨start, continues, normalized⟩ := canonical
        have all := List.all_eq_true.mp continues
        have boundary : isWordContinue ' ' = false := rfl
        have take : (rest ++ ' ' :: render tokens).takeWhile isWordContinue = rest := by
          simp [List.takeWhile_append_of_pos all, boundary]
        have drop : (rest ++ ' ' :: render tokens).dropWhile isWordContinue =
            ' ' :: render tokens := by
          simp [List.dropWhile_append_of_pos all, boundary]
        have lex := Lexes.word (rest := rest ++ ' ' :: render tokens) start (drop ▸ spaced)
        simpa only [take, normalized, render, Token.chars, chars, List.cons_append] using lex

end Silmaril.Proofs.Machine.SQLite.Tokenizer
