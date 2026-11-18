module

public import Silmaril.Formats.SExp.Dotted.Defs
import Silmaril.Proofs.Formats.SExp.Lexical.Basic

/-! # Proofs: the dotted text syntax lexes its printed tokens back -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Dotted

open Silmaril.Formats Silmaril.Formats.SExpReader Silmaril.Formats.SExpLexical
open Silmaril.Formats.DottedSExp
open Silmaril.Proofs.Formats.SExp.Lexical

theorem skip_space (s : List Char) : skip false (' ' :: s) = skip false s := by
  simp [skip, isSpace]

theorem skip_head {c : Char} (r : List Char) (hs : isSpace c = false) (hc : c ≠ ';') :
    skip false (c :: r) = c :: r := by
  simp [skip, hs, hc]

theorem step_space (s : List Char) : step (' ' :: s) = step s := by
  unfold step; rw [skip_space]

theorem delim_of_follows {rest : List Char} (h : Follows text rest) :
    ∀ c r, rest = c :: r → (!isDelimiter c) = false := by
  rintro c r rfl
  rcases h with h | ⟨r', h⟩ | ⟨_, r', h⟩
  · cases h
  · cases h; decide
  · simp only [text, List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; decide

theorem step_quoted {q : Char} {w rest : List Char} (hq : q = '"' ∨ q = '|') :
    step (q :: (escapeMnemonic q w ++ q :: rest)) =
      if q = '"' then .token (.atom (.string (String.ofList w))) rest
      else .token (.atom (.symbol (String.ofList w))) rest := by
  have hesc : escape '\\' = some '\\' := by decide
  rcases hq with rfl | rfl
  · have hr := readQuoted_mnemonic (q := '"') hesc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w rest
    unfold step
    rw [skip_head _ (by decide) (by decide)]
    simp [hr]
  · have hr := readQuoted_mnemonic (q := '|') hesc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w rest
    unfold step
    rw [skip_head _ (by decide) (by decide)]
    simp [hr]

theorem step_atom (a : Atom) (rest : List Char) (hrest : Follows text rest) :
    step (text (.atom a) ++ rest) = .token (.atom a) rest := by
  cases a with
  | string s =>
      have := step_quoted (q := '"') (w := s.toList) (rest := rest) (Or.inl rfl)
      simp only [ite_true, String.ofList_toList] at this
      simpa [text, atomText] using this
  | symbol s =>
      simp only [text, atomText]
      split
      · rename_i hb
        simp only [bare, Bool.and_eq_true, decide_eq_true_eq, ne_eq, List.all_eq_true] at hb
        obtain ⟨⟨hne, hall⟩, hdot⟩ := hb
        obtain ⟨c, r, hcr⟩ : ∃ c r, s.toList = c :: r := by
          cases h : s.toList with
          | nil => exact absurd h hne
          | cons c r => exact ⟨c, r, rfl⟩
        have hc : (!isDelimiter c) = true := hall c (by simp [hcr])
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, isDelimiter, Bool.or_eq_false_iff,
          decide_eq_false_iff_not] at hc
        obtain ⟨⟨⟨⟨⟨hsp, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hc
        have htake := takeToken_append (p := fun c => !isDelimiter c) (w := s.toList)
          (fun d hd => hall d hd) (delim_of_follows hrest)
        unfold step
        rw [hcr, List.cons_append, skip_head _ hsp h4]
        rw [hcr, List.cons_append] at htake
        simp only [h1, h2, h3, h5, ite_false, htake]
        rw [← hcr, ite_eq_right hdot, String.ofList_toList]
      · have := step_quoted (q := '|') (w := s.toList) (rest := rest) (Or.inr rfl)
        simp only [String.ofList_toList] at this
        simpa using this

theorem step_dot (rest : List Char) (hrest : Follows text rest) :
    step (text .dot ++ rest) = .token .dot rest := by
  have htake := takeToken_append (p := fun c => !isDelimiter c) (w := ['.'])
    (by decide) (delim_of_follows hrest)
  unfold step
  simp only [text, List.cons_append, List.nil_append]
  rw [skip_head _ (by decide) (by decide)]
  simp only [List.cons_append, List.nil_append] at htake
  simp [htake]

theorem printLaws : PrintLaws syntaxNotation lexer text where
  size_eq _ := rfl
  space := step_space
  eof := rfl
  atom a rest _ h := step_atom a rest h
  dot _ rest h := step_dot rest h
  openList rest := by
    unfold lexer; dsimp only; unfold step
    simp [text, skip_head _ (by decide : isSpace '(' = false) (by decide : '(' ≠ ';'),
      syntaxNotation]
  openColl m c d rest h := by cases h
  close c rest := by
    unfold lexer; dsimp only; unfold step
    simp [text, skip_head _ (by decide : isSpace ')' = false) (by decide : ')' ≠ ';')]
  «prefix» p rest h := by cases h
  nonempty t := by
    cases t with
    | atom a =>
        cases a with
        | string => simp [text, atomText]
        | symbol s =>
            simp only [text, atomText]
            split
            · rename_i hb
              simp only [bare, Bool.and_eq_true, decide_eq_true_eq] at hb
              exact hb.1.1
            · simp
    | _ => simp [text]

@[simp] theorem role_eq (a : Atom) : syntaxNotation.role a = .plain := rfl
@[simp] theorem listDotted_eq : syntaxNotation.listDotted = true := rfl

theorem wf_all (e : Datum) :
    syntaxNotation.wf e = true ∧ syntaxNotation.wfItems true false e = true := by
  induction e with
  | nil => exact ⟨rfl, rfl⟩
  | atom a => exact ⟨rfl, rfl⟩
  | cons x r ihx ihr =>
      cases x with
      | atom m =>
          exact ⟨by simp [Notation.wf, ihr.2], by simp [Notation.wfItems, ihr.2]⟩
      | nil =>
          exact ⟨by simp [Notation.wf, ihr.2], by simp [Notation.wfItems, Notation.wf, ihr.2]⟩
      | cons =>
          exact ⟨by simp [Notation.wf, ihx.1, ihr.2], by simp [Notation.wfItems, ihx.1, ihr.2]⟩

end Silmaril.Proofs.Formats.SExp.Dotted
