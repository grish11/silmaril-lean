module

public import Silmaril.Formats.SExp.Dotted.Defs
import Silmaril.Proofs.Formats.SExp.Reader.Basic
import Silmaril.Proofs.Formats.SExp.Lexical.Basic
import Silmaril.Proofs.Formats.SExp.Dotted.Basic

/-! # Proofs: the dotted lexer implements the declarative lexical grammar -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Dotted

open Silmaril.Formats Silmaril.Formats.SExpReader Silmaril.Formats.SExpLexical
open Silmaril.Formats.DottedSExp Silmaril.Proofs.Formats.SExp.Reader
open Silmaril.Proofs.Formats.SExp.Lexical

/-! ## Atmosphere -/

theorem skip_comment {body : List Char} (h : '\n' ∉ body) (r : List Char) :
    skip true (body ++ '\n' :: r) = skip false r := by
  induction body with
  | nil => simp [skip]
  | cons c body ih =>
      simp only [List.mem_cons, not_or] at h
      simp [skip, Ne.symm h.1, ih h.2]

theorem skip_comment_end {body : List Char} (h : '\n' ∉ body) : skip true body = [] := by
  induction body with
  | nil => rfl
  | cons c body ih =>
      simp only [List.mem_cons, not_or] at h
      simp [skip, Ne.symm h.1, ih h.2]

/-- The first character after atmosphere. -/
def Starts (r : List Char) : Prop := ∀ c r', r = c :: r' → isSpace c = false ∧ c ≠ ';'

theorem skip_gap_append {a : List Char} (ha : Gap a) (rest : List Char) :
    skip false (a ++ rest) = skip false rest := by
  induction ha with
  | nil => rfl
  | space hc _ ih => simp [skip, hc, ih]
  | comment hb _ ih =>
      simp only [List.cons_append, List.append_assoc]
      simp [skip, isSpace, skip_comment hb, ih]

theorem skip_starts {rest : List Char} (hr : Starts rest) : skip false rest = rest := by
  cases rest with
  | nil => rfl
  | cons c r => obtain ⟨h1, h2⟩ := hr c r rfl; simp [skip, h1, h2]

theorem skip_gap {a : List Char} (ha : Gap a) {rest : List Char} (hr : Starts rest) :
    skip false (a ++ rest) = rest := by
  rw [skip_gap_append ha, skip_starts hr]

theorem skip_trailing {a : List Char} (ha : Trailing a) : skip false a = [] := by
  cases ha with
  | gap g => simpa [skip] using skip_gap_append g []
  | comment g hb =>
      rw [skip_gap_append g]
      simp [skip, isSpace, skip_comment_end hb]

theorem skip_true_sound : ∀ {s r : List Char}, skip true s = r →
    (∃ body rest, s = body ++ '\n' :: rest ∧ '\n' ∉ body ∧ skip false rest = r) ∨
      ('\n' ∉ s ∧ r = [])
  | [], r, h => by simp [skip] at h; exact Or.inr ⟨by simp, h⟩
  | c :: s, r, h => by
      simp only [skip] at h
      split at h
      · rename_i hc; subst hc; exact Or.inl ⟨[], s, rfl, by simp, h⟩
      · rename_i hc
        rcases skip_true_sound h with ⟨body, rest, rfl, hb, hs⟩ | ⟨hn, rfl⟩
        · exact Or.inl ⟨c :: body, rest, rfl, by simp [Ne.symm hc, hb], hs⟩
        · exact Or.inr ⟨by simp [Ne.symm hc, hn], rfl⟩

theorem skip_sound : ∀ (n : Nat) {s r : List Char}, s.length ≤ n → skip false s = r →
    ∃ a, s = a ++ r ∧ ((r = [] ∧ Trailing a) ∨ (Starts r ∧ r ≠ [] ∧ Gap a))
  | _, [], r, _, h => by simp [skip] at h; subst h; exact ⟨[], rfl, Or.inl ⟨rfl, .gap .nil⟩⟩
  | 0, _ :: _, _, hl, _ => by simp at hl
  | n + 1, c :: s, r, hl, h => by
      simp only [skip] at h
      split at h
      · rename_i hc
        obtain ⟨a, rfl, hcase⟩ := skip_sound n (by simp at hl; omega) h
        refine ⟨c :: a, rfl, ?_⟩
        rcases hcase with ⟨rfl, ht⟩ | ⟨hs, hne, hg⟩
        · left; refine ⟨rfl, ?_⟩
          cases ht with
          | gap g => exact .gap (.space hc g)
          | comment g hb => exact .comment (a := c :: _) (.space hc g) hb
        · exact Or.inr ⟨hs, hne, .space hc hg⟩
      split at h
      · rename_i _ hsemi
        subst hsemi
        rcases skip_true_sound h with ⟨body, rest, rfl, hb, hs⟩ | ⟨hn, rfl⟩
        · obtain ⟨a, rfl, hcase⟩ := skip_sound n
            (by simp at hl ⊢; omega) hs
          refine ⟨';' :: body ++ '\n' :: a, by simp, ?_⟩
          rcases hcase with ⟨rfl, ht⟩ | ⟨hs', hne, hg⟩
          · left; refine ⟨rfl, ?_⟩
            cases ht with
            | gap g => exact .gap (.comment hb g)
            | comment g hb' =>
                have := Trailing.comment (.comment hb g) hb'
                simpa [List.append_assoc] using this
          · exact Or.inr ⟨hs', hne, .comment hb hg⟩
        · exact ⟨';' :: s, by simp, Or.inl ⟨rfl, by simpa using Trailing.comment .nil hn⟩⟩
      · rename_i hsp hsemi
        subst h
        refine ⟨[], rfl, Or.inr ⟨?_, by simp, .nil⟩⟩
        intro c' r' h; cases h; exact ⟨by simpa using hsp, hsemi⟩

/-! ## Quoted bodies -/

theorem readQuoted_body {q : Char} (hq : q ≠ '\\') {w sp : List Char} (h : Body q w sp)
    (rest : List Char) : readQuoted q escape (sp ++ q :: rest) = some (w, rest) := by
  have hbq : ('\\' = q) = False := by simp [Ne.symm hq]
  induction h with
  | nil => simp [readQuoted]
  | plain h1 h2 _ ih => simp [readQuoted, h1, h2, ih]
  | escaped he _ ih => simp [readQuoted, readEscape, hbq, he, ih]

theorem body_of_readQuoted {q : Char} : ∀ {cs w rest : List Char},
    readQuoted q escape cs = some (w, rest) → ∃ sp, cs = sp ++ q :: rest ∧ Body q w sp
  | [], w, rest, h => by simp [readQuoted] at h
  | c :: cs, w, rest, h => by
      simp only [readQuoted] at h
      split at h
      · rename_i hc; subst hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], rfl, .nil⟩
      split at h
      · rename_i hcq hcb
        subst hcb
        cases cs with
        | nil => simp [readEscape] at h
        | cons e cs =>
            simp only [readEscape] at h
            split at h
            · rename_i d hd
              cases hr : readQuoted q escape cs with
              | none => rw [hr] at h; cases h
              | some p =>
                  obtain ⟨w', rest'⟩ := p
                  rw [hr] at h
                  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  obtain ⟨sp, rfl, hb⟩ := body_of_readQuoted hr
                  exact ⟨'\\' :: e :: sp, rfl, .escaped hd hb⟩
            · cases h
      · rename_i hcq hcb
        cases hr : readQuoted q escape cs with
        | none => rw [hr] at h; cases h
        | some p =>
            obtain ⟨w', rest'⟩ := p
            rw [hr] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨sp, rfl, hb⟩ := body_of_readQuoted hr
            exact ⟨c :: sp, rfl, .plain hcq hcb hb⟩

/-! ## Tokens -/

theorem takeToken_sound {p : Char → Bool} : ∀ {cs w r : List Char},
    takeToken p cs = (w, r) → cs = w ++ r ∧ (∀ c ∈ w, p c = true) ∧
      ∀ c r', r = c :: r' → p c = false
  | [], w, r, h => by simp [takeToken] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | c :: cs, w, r, h => by
      simp only [takeToken] at h
      split at h
      · rename_i hc
        cases ht : takeToken p cs with
        | mk w' r' =>
            rw [ht] at h
            simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨h1, h2, h3⟩ := takeToken_sound ht
            refine ⟨by simp [h1], ?_, h3⟩
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact hc
            · exact h2 x hx
      · rename_i hc
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, by simp, ?_⟩
        intro x r' h; cases h; simpa using hc

theorem step_sound {s r : List Char} {t : Token Atom Unit} (h : step s = .token t r) :
    ∃ a w, s = a ++ w ++ r ∧ Gap a ∧ Lexeme t w r := by
  unfold step at h
  cases hs : skip false s with
  | nil => rw [hs] at h; cases h
  | cons c r₀ =>
      rw [hs] at h
      obtain ⟨a, rfl, hcase⟩ := skip_sound _ le_rfl hs
      have hg : Gap a := by
        rcases hcase with ⟨h, -⟩ | ⟨-, -, hg⟩
        · cases h
        · exact hg
      have hst : isSpace c = false ∧ c ≠ ';' := by
        rcases hcase with ⟨h, -⟩ | ⟨hs', -, -⟩
        · cases h
        · exact hs' c r₀ rfl
      simp only at h
      split at h
      · rename_i hc; subst hc; cases h
        exact ⟨a, ['('], by simp, hg, .open⟩
      split at h
      · rename_i _ hc; subst hc; cases h
        exact ⟨a, [')'], by simp, hg, .close⟩
      split at h
      · rename_i _ _ hc; subst hc
        split at h
        · rename_i w r' hq
          cases h
          obtain ⟨sp, rfl, hb⟩ := body_of_readQuoted hq
          exact ⟨a, '"' :: sp ++ ['"'], by simp, hg, .string hb⟩
        · cases h
      split at h
      · rename_i _ _ _ hc; subst hc
        split at h
        · rename_i w r' hq
          cases h
          obtain ⟨sp, rfl, hb⟩ := body_of_readQuoted hq
          exact ⟨a, '|' :: sp ++ ['|'], by simp, hg, .quoted hb⟩
        · cases h
      · rename_i h1 h2 h3 h4
        have hcd : isDelimiter c = false := by
          simp [isDelimiter, hst.1, hst.2, h1, h2, h3, h4]
        cases ht : takeToken (fun c => !isDelimiter c) (c :: r₀) with
        | mk w r' =>
            rw [ht] at h
            obtain ⟨heq, hall, hbd⟩ := takeToken_sound ht
            have hwne : w ≠ [] := by
              intro hw; subst hw
              have := hbd c r₀ (by simpa using heq.symm)
              simp [hcd] at this
            have hbound : Boundary r' := by
              intro x r'' hr; simpa using hbd x r'' hr
            have hall' : ∀ x ∈ w, isDelimiter x = false := by
              intro x hx; simpa using hall x hx
            simp only at h
            split at h
            · rename_i hdot; cases h; subst hdot
              exact ⟨a, ['.'], by rw [heq]; simp, hg, .dot hbound⟩
            · rename_i hdot; cases h
              exact ⟨a, w, by rw [heq]; simp, hg, .bare hwne hall' hdot hbound⟩

theorem step_eof_sound {s : List Char} (h : step s = .eof) : Trailing s := by
  unfold step at h
  cases hs : skip false s with
  | nil =>
      obtain ⟨a, rfl, hcase⟩ := skip_sound _ le_rfl hs
      rcases hcase with ⟨-, ht⟩ | ⟨-, hne, -⟩
      · simpa using ht
      · exact absurd rfl hne
  | cons c r =>
      rw [hs] at h
      simp only at h
      split at h; · cases h
      split at h; · cases h
      split at h
      · split at h <;> cases h
      split at h
      · split at h <;> cases h
      · cases ht : takeToken (fun c => !isDelimiter c) (c :: r) with
        | mk w r' =>
            rw [ht] at h
            simp only at h
            split at h <;> cases h

theorem lexeme_starts {t : Token Atom Unit} {w s : List Char} (h : Lexeme t w s) :
    ∃ c w', w = c :: w' ∧ isSpace c = false ∧ c ≠ ';' := by
  cases h with
  | «open» => exact ⟨_, _, rfl, by decide, by decide⟩
  | close => exact ⟨_, _, rfl, by decide, by decide⟩
  | string => exact ⟨_, _, rfl, by decide, by decide⟩
  | quoted => exact ⟨_, _, rfl, by decide, by decide⟩
  | dot => exact ⟨_, _, rfl, by decide, by decide⟩
  | @bare w s hne hall _ _ =>
      obtain ⟨c, w', rfl⟩ : ∃ c w', w = c :: w' := by
        cases w with
        | nil => exact absurd rfl hne
        | cons c w' => exact ⟨c, w', rfl⟩
      have hc := hall c (by simp)
      simp only [isDelimiter, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc
      exact ⟨c, w', rfl, hc.1.1.1.1.1, hc.1.2⟩

theorem step_complete {a w s : List Char} {t : Token Atom Unit} (ha : Gap a)
    (hl : Lexeme t w s) : step (a ++ w ++ s) = .token t s := by
  obtain ⟨c, w', hw, hc1, hc2⟩ := lexeme_starts hl
  have hskip : skip false (a ++ w ++ s) = w ++ s := by
    rw [List.append_assoc]
    exact skip_gap ha (by intro x r h; rw [hw] at h; cases h; exact ⟨hc1, hc2⟩)
  unfold step
  rw [hskip]
  cases hl with
  | «open» => simp
  | close => simp
  | string hb =>
      simp [readQuoted_body (by decide) hb]
  | quoted hb =>
      simp [readQuoted_body (by decide) hb]
  | dot hb =>
      have ht := takeToken_append (p := fun c => !isDelimiter c) (w := ['.']) (rest := s)
        (by decide) (by intro x r h; simpa using hb x r h)
      simp only [List.cons_append, List.nil_append] at ht ⊢
      simp [ht]
  | bare hne hall hdot hb =>
      subst hw
      have hcd : isDelimiter c = false := hall c (by simp)
      simp only [isDelimiter, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hcd
      have ht := takeToken_append (p := fun c => !isDelimiter c) (w := c :: w') (rest := s)
        (by intro x hx; simpa using hall x hx) (by intro x r h; simpa using hb x r h)
      simp only [List.cons_append] at ht ⊢
      simp [hcd.1.1.1.1.2, hcd.1.1.1.2, hcd.1.1.2, hcd.2, ht, hdot]

theorem step_trailing {a : List Char} (h : Trailing a) : step a = .eof := by
  unfold step; rw [skip_trailing h]

theorem lexeme_ne_nil {t : Token Atom Unit} {w s : List Char} (h : Lexeme t w s) : w ≠ [] := by
  obtain ⟨c, w', rfl, -⟩ := lexeme_starts h; simp

/-- **The lexer implements the declarative lexical grammar.** -/
theorem emits_iff_tokenizes (s : List Char) (ts : List (Token Atom Unit)) :
    (∃ r, lexer.Emits s ts r ∧ (lexer.next r).isEof = true) ↔ Tokenizes s ts := by
  constructor
  · rintro ⟨r, he, heof⟩
    induction he with
    | nil s =>
        apply Tokenizes.done
        apply step_eof_sound
        unfold Lexer.next at heof
        cases hs : lexer.step s with
        | token t r => rw [hs] at heof; simp only at heof; split at heof <;> cases heof
        | eof => exact hs
        | error => rw [hs] at heof; cases heof
    | cons hn _ ih =>
        obtain ⟨hs, -⟩ := next_token hn
        obtain ⟨a, w, rfl, hg, hl⟩ := step_sound hs
        exact .token hg hl (ih heof)
  · intro h
    induction h with
    | done ht =>
        exact ⟨_, .nil _, by simp [Lexer.next, lexer, step_trailing ht, Step.isEof]⟩
    | token hg hl _ ih =>
        obtain ⟨r, he, heof⟩ := ih
        refine ⟨r, .cons (next_of_step (step_complete hg hl) ?_) he, heof⟩
        have := lexeme_ne_nil hl
        simp only [lexer, List.length_append]
        have := List.length_pos_iff.2 this
        omega

end Silmaril.Proofs.Formats.SExp.Dotted
