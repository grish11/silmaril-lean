module

public import Silmaril.Formats.SExp.Dotted.Defs
public import Silmaril.Formats.SExp.Printer
import Silmaril.Proofs.Formats.SExp.Reader.Basic
import Silmaril.Proofs.Formats.SExp.Dotted.Basic

/-! # Proofs: the dotted printer has the older printer's layout -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Dotted

open Silmaril.Formats Silmaril.Formats.SExpReader Silmaril.Formats.SExpLexical
open Silmaril.Formats.DottedSExp Silmaril.Proofs.Formats.SExp.Reader

mutual
  /-- The layout of `SExpPrinter.printSExp2With`, with the dotted atom text. -/
  def direct : Datum → List Char
    | .nil => ['(', ')']
    | .atom a => atomText a
    | .cons x r => '(' :: direct x ++ directTail r ++ [')']

  def directTail : Datum → List Char
    | .nil => []
    | .cons x r => ' ' :: direct x ++ directTail r
    | .atom a => ' ' :: '.' :: ' ' :: atomText a
end

variable {A : Type} {C : Type}

theorem render_append (text : Token A C → List Char) :
    ∀ (ts us : List (Token A C)) (t u : Token A C), ts.getLast? = some t → us.head? = some u →
      render text (ts ++ us) = render text ts ++ sep t u ++ render text us
  | [], _, _, _, h, _ => by simp at h
  | [t'], u' :: us, t, u, ht, hu => by
      simp only [List.getLast?_singleton, Option.some.injEq] at ht
      simp only [List.head?_cons, Option.some.injEq] at hu
      subst ht; subst hu
      simp [render]
  | t' :: t'' :: ts, us, t, u, ht, hu => by
      have ih := render_append text (t'' :: ts) us t u (by simpa using ht) hu
      show render text (t' :: (t'' :: ts ++ us)) = _
      simp only [List.cons_append, render] at ih ⊢
      rw [ih]; simp [List.append_assoc]

/-- Separator before the remainder of a list: none before the closer. -/
def lead (ts : List (Token Atom Unit)) : List Char :=
  match ts with
  | .close _ :: _ => []
  | _ => [' ']

theorem tokens_shape (e : Datum) :
    (∃ t ts, syntaxNotation.tokens e = t :: ts ∧ t.isClose = false) ∧
    ∃ init t, syntaxNotation.tokens e = init ++ [t] ∧ (t.isClose = true ∨ ∃ a, t = .atom a) := by
  have hg := (tokens_gram syntaxNotation e).1 (wf_all e).1
  obtain ⟨t, ts, h, hs⟩ := gram_datum_cons hg rfl
  refine ⟨⟨t, ts, h, ?_⟩, gram_endsWell hg⟩
  cases t <;> simp_all [Token.startsDatum, Token.isClose]

theorem sep_last {t u : Token Atom Unit} (ht : t.isClose = true ∨ ∃ a, t = .atom a) :
    sep t u = lead [u] := by
  rcases ht with ht | ⟨a, rfl⟩
  · cases t <;> simp [Token.isClose] at ht
    cases u <;> simp [sep, lead, Token.isOpen, Token.isClose, Token.isPrefix]
  · cases u <;> simp [sep, lead, Token.isOpen, Token.isClose, Token.isPrefix]

theorem render_tokens (e : Datum) :
    render text (syntaxNotation.tokens e) = direct e ∧
    (lead (syntaxNotation.itemTokens () e) ++ render text (syntaxNotation.itemTokens () e) =
      directTail e ++ [')']) := by
  induction e with
  | nil => exact ⟨by simp [Notation.tokens, render, sep, Token.isOpen, text, direct, syntaxNotation],
      by simp [Notation.itemTokens, lead, render, text, directTail]⟩
  | atom a => exact ⟨by simp [Notation.tokens, render, text, direct],
      by simp [Notation.itemTokens, lead, render, sep, Token.isOpen, Token.isClose, Token.isPrefix,
        text, directTail]⟩
  | cons x r ihx ihr =>
      obtain ⟨⟨t₀, ts₀, hx₀, hc₀⟩, ⟨init, tl, hxl, htl⟩⟩ := tokens_shape x
      -- the item tokens of `r` start with something
      have hitems : ∃ u us, syntaxNotation.itemTokens () r = u :: us := by
        cases r with
        | nil => exact ⟨_, _, rfl⟩
        | atom => exact ⟨_, _, rfl⟩
        | cons y z =>
            cases y with
            | atom m => exact ⟨.atom m, syntaxNotation.itemTokens () z,
                by simp [Notation.itemTokens]⟩
            | nil =>
                obtain ⟨⟨t, ts, h, -⟩, -⟩ := tokens_shape .nil
                exact ⟨t, ts ++ _, by rw [itemTokens_cons_of_not_atom _ (by simp), h]; rfl⟩
            | cons a b =>
                obtain ⟨⟨t, ts, h, -⟩, -⟩ := tokens_shape (.cons a b)
                exact ⟨t, ts ++ _, by rw [itemTokens_cons_of_not_atom _ (by simp), h]; rfl⟩
      obtain ⟨u, us, hu⟩ := hitems
      have hcat : render text (syntaxNotation.tokens x ++ syntaxNotation.itemTokens () r) =
          direct x ++ directTail r ++ [')'] := by
        rw [render_append text _ _ tl u (by rw [hxl]; simp) (by rw [hu]; rfl), ihx.1,
          sep_last htl]
        have : lead [u] = lead (syntaxNotation.itemTokens () r) := by
          rw [hu]; cases u <;> rfl
        rw [this, List.append_assoc, ihr.2, List.append_assoc]
      have htok : syntaxNotation.tokens (.cons x r) =
          .open none () true :: (syntaxNotation.tokens x ++ syntaxNotation.itemTokens () r) := by
        cases x with
        | atom m => simp [Notation.tokens, syntaxNotation]
        | nil => exact tokens_cons_of_not_atom _ (by simp)
        | cons => exact tokens_cons_of_not_atom _ (by simp)
      have hit : syntaxNotation.itemTokens () (.cons x r) =
          syntaxNotation.tokens x ++ syntaxNotation.itemTokens () r := by
        cases x with
        | atom m => simp [Notation.itemTokens, Notation.tokens, syntaxNotation]
        | nil => exact itemTokens_cons_of_not_atom _ (by simp)
        | cons => exact itemTokens_cons_of_not_atom _ (by simp)
      have hL : syntaxNotation.tokens x ++ syntaxNotation.itemTokens () r =
          t₀ :: (ts₀ ++ syntaxNotation.itemTokens () r) := by rw [hx₀]; rfl
      refine ⟨?_, ?_⟩
      · rw [htok, hL]
        simp only [render, sep, Token.isOpen, Bool.true_or, ite_true]
        rw [← hL, hcat]
        simp [text, direct]
      · rw [hit, hL]
        have hlead : lead (t₀ :: (ts₀ ++ syntaxNotation.itemTokens () r)) = [' '] := by
          cases t₀ <;> simp_all [lead, Token.isClose]
        rw [hlead, ← hL, hcat]
        simp [directTail]

theorem escapeChar_toList (c : Char) :
    (SExpPrinter.escapeChar c).toList = escapeMnemonic '"' [c] := by
  unfold SExpPrinter.escapeChar
  split <;> simp_all [escapeMnemonic]

theorem escapeMnemonic_append (q : Char) : ∀ (a b : List Char),
    escapeMnemonic q (a ++ b) = escapeMnemonic q a ++ escapeMnemonic q b
  | [], b => rfl
  | c :: a, b => by simp [escapeMnemonic, escapeMnemonic_append q a b]

theorem join_escapeChar (l : List Char) :
    List.flatMap String.toList (l.map SExpPrinter.escapeChar) = escapeMnemonic '"' l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
      simp only [List.map_cons, List.flatMap_cons, ih, escapeChar_toList]
      rw [← escapeMnemonic_append]; rfl

theorem quote_toList (s : String) :
    (SExpPrinter.quote s).toList = atomText (.string s) := by
  simp [SExpPrinter.quote, atomText, join_escapeChar]

theorem legacy_print : ∀ v : SExp2 String,
    (SExpPrinter.printSExp2With SExpPrinter.quote v).toList = direct (v.map .string) ∧
    (SExpPrinter.printTailWith SExpPrinter.quote v).toList = directTail (v.map .string)
  | .nil => by simp [SExpPrinter.printSExp2With, SExpPrinter.printTailWith, SExp2.map, direct,
      directTail]
  | .atom s => by
      refine ⟨by simp [SExpPrinter.printSExp2With, SExp2.map, direct, quote_toList], ?_⟩
      simp [SExpPrinter.printTailWith, SExpPrinter.printSExp2With, SExp2.map, directTail,
        quote_toList]
  | .cons x r => by
      have hx := (legacy_print x).1
      have hr := (legacy_print r).2
      refine ⟨?_, ?_⟩
      · simp [SExpPrinter.printSExp2With, SExp2.map, direct, hx, hr]
      · simp [SExpPrinter.printTailWith, SExp2.map, directTail, hx, hr]

/-- **The dotted printer writes strings exactly as the older printer does.** -/
theorem print_map_string (v : SExp2 String) :
    DottedSExp.print (v.map .string) = SExpPrinter.printSExp2 v := by
  apply String.toList_inj.1
  simp only [DottedSExp.print, String.toList_ofList, SExpPrinter.printSExp2,
    SExpReader.print, (render_tokens _).1, (legacy_print v).1]

end Silmaril.Proofs.Formats.SExp.Dotted
