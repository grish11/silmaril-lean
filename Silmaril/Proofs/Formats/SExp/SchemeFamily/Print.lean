module

public import Silmaril.Formats.SExp.SchemeFamily.Defs
import Silmaril.Proofs.Formats.SExp.Lexical.Basic
public import Silmaril.Proofs.Formats.SExp.SchemeFamily.Basic

/-! # Proofs: every Scheme-family dialect lexes its printed tokens back -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.SchemeFamily

open Silmaril.Formats Silmaril.Formats.SExpReader Silmaril.Formats.SExpLexical
open Silmaril.Formats.SchemeFamily Silmaril.Formats.SchemeFamily.Dialect
open Silmaril.Proofs.Formats.SExp.Lexical

variable {C : Type} {D : Dialect C}

theorem step_bare (hL : D.Laws) {w rest : List Char} (hw : ∀ x ∈ w, D.bareChar x = true)
    (hne : w ≠ []) (hrest : Delimited D rest) (hdot : w ≠ ['.'])
    (hfirst : ∀ c r, w = c :: r → c ≠ '\'' ∧ c ≠ '`' ∧ c ≠ ',' ∧ c ≠ '#') :
    D.step (w ++ rest) =
      match D.classify w with
      | some a => .token (.atom a) rest
      | none => .error := by
  obtain ⟨c, r, rfl⟩ : ∃ c r, w = c :: r := by
    cases w with
    | nil => exact absurd rfl hne
    | cons c r => exact ⟨c, r, rfl⟩
  have hc := hw c (by simp)
  obtain ⟨h1, h2, h3, h4⟩ := hfirst c r rfl
  have hsemi : c ≠ ';' := ne_delim (not_delim_of_bareChar hc) hL.delim_special.1
  rw [List.cons_append, step_of_skip (skip_stop _ (not_whitespace_of_bareChar hL hc) hsemi h4),
    dispatch_bare hL _ hc h1 h2 h3 h4, ← List.cons_append]
  exact bare_append hw hne hrest hdot

theorem step_numeral (hL : D.Laws) {w rest : List Char} (hnum : NumHead w)
    (hchars : ∀ x ∈ w, D.bareChar x = true) (hrest : Delimited D rest) :
    D.step (w ++ rest) =
      match D.classify w with
      | some a => .token (.atom a) rest
      | none => .error := by
  refine step_bare hL hchars ?_ hrest (ne_dot_of_numHead hnum) ?_
  · obtain ⟨c, r, rfl, -⟩ := hnum; simp
  · intro c r hw
    obtain ⟨c', r', h', hc⟩ := hnum
    rw [hw] at h'
    cases h'
    rcases hc with hc | ⟨rfl, -⟩
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> simp [Char.isDigit] at hc
    · decide

theorem step_quoted {q : Char} {r : List Char} (hq : q = '"' ∨ q = '|') :
    D.step (q :: r) = D.dispatch q r := by
  have hw : isWhitespace q = false := by rcases hq with rfl | rfl <;> decide
  have hs : q ≠ ';' := by rcases hq with rfl | rfl <;> decide
  have hh : q ≠ '#' := by rcases hq with rfl | rfl <;> decide
  rw [step_of_skip (skip_stop _ hw hs hh)]

theorem step_hash (hL : D.Laws) {d : Char} {r : List Char} (hd : d ≠ '|') :
    D.step ('#' :: d :: r) = D.hash (d :: r) := by
  rw [step_of_skip (skip_hash r hd)]
  simp [Dialect.dispatch, hL.opener_special.2.2, hL.closer_special.2.2]

theorem step_atom (hL : D.Laws) (a : Atom) (rest : List Char) (hrole : D.role a = .plain)
    (hfollow : Follows D.text rest) :
    D.step (D.text (.atom a) ++ rest) = .token (.atom a) rest := by
  have hrest := delimited_of_follows hL hfollow
  have hnb := not_bareChar_of_delimited hrest
  cases a with
  | symbol s =>
      simp only [Dialect.text, Dialect.atomText]
      split
      · rename_i hb
        simp only [Dialect.bareSymbol] at hb
        split at hb
        · cases hb
        · rename_i c r' hcr
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hb
          obtain ⟨⟨⟨⟨⟨⟨hall, h1⟩, h2⟩, h3⟩, h4⟩, hdot⟩, hcls⟩ := hb
          rw [step_bare hL (List.all_eq_true.1 hall) (by simp [hcr]) hrest hdot
            (by intro c' r'' h; rw [hcr] at h; cases h; exact ⟨h1, h2, h3, h4⟩), hcls]
          simp
      · have hwr : D.writableName s.toList = true := by
          simp only [Dialect.role] at hrole
          split at hrole
          · assumption
          · cases hrole
        have heq : '|' :: escapeQuoted '|' s.toList ++ ['|'] ++ rest =
            '|' :: (escapeQuoted '|' s.toList ++ '|' :: rest) := by simp
        rw [heq, step_quoted (Or.inr rfl)]
        simp [Dialect.dispatch, hL.opener_special.2.1, hL.closer_special.2.1,
          hL.bar s.toList rest hwr]
  | keyword s =>
      have hwr : D.keywords = true ∧ D.writableName s.toList = true := by
        simp only [Dialect.role] at hrole
        split at hrole
        · simpa using (by assumption : (D.keywords && D.writableName s.toList) = true)
        · cases hrole
      simp only [Dialect.text, Dialect.atomText]
      split
      · rename_i hb
        obtain ⟨hne, hall⟩ := hb
        obtain ⟨c, r', hcr⟩ : ∃ c r', s.toList = c :: r' := by
          cases h : s.toList with
          | nil => exact absurd h hne
          | cons c r' => exact ⟨c, r', rfl⟩
        have hall' := List.all_eq_true.1 hall
        have hcbar := (ne_of_bareChar (hall' c (by simp [hcr]))).1
        have hkw : takeToken D.bareChar (c :: (r' ++ rest)) = (c :: r', rest) := by
          rw [← List.cons_append, ← hcr]; exact takeToken_append hall' hnb
        have hhead : (rest.head? = some '|' || rest.head? = some '\\') = false := by
          cases rest with
          | nil => rfl
          | cons c r =>
              obtain ⟨-, h1, h2, -⟩ := hrest c r rfl
              simp [h1, h2]
        have heq : ('#' :: ':' :: s.toList) ++ rest = '#' :: ':' :: c :: (r' ++ rest) := by
          simp [hcr]
        rw [heq, step_hash hL (by decide)]
        simp only [Dialect.hash, hwr.1, Dialect.hashKeyword, hcbar, Dialect.keywordWord, hkw]
        simp only [reduceCtorEq, ite_false, Bool.and_true, Bool.false_or, hhead,
          List.cons_ne_nil, decide_false]
        simp [← hcr]
      · have heq : '#' :: ':' :: '|' :: escapeQuoted '|' s.toList ++ ['|'] ++ rest =
            '#' :: ':' :: '|' :: (escapeQuoted '|' s.toList ++ '|' :: rest) := by simp
        rw [heq, step_hash hL (by decide)]
        simp [Dialect.hash, hwr.1, Dialect.hashKeyword, hL.bar s.toList rest hwr.2]
  | boolean b =>
      have ht := takeToken_append (p := D.bareChar) (w := [if b then 't' else 'f']) (rest := rest)
        (by cases b <;> simp [bareChar_of_notDelim hL])
        hnb
      cases b
      · simp only [Dialect.text, Dialect.atomText, Bool.false_eq_true, ite_false]
        rw [List.cons_append, List.cons_append, step_hash hL (by decide)]
        simp only [Bool.false_eq_true, ite_false, List.singleton_append] at ht
        simp [Dialect.hash, Dialect.hashWord, ht]
      · simp only [Dialect.text, Dialect.atomText, ite_true]
        rw [List.cons_append, List.cons_append, step_hash hL (by decide)]
        simp only [ite_true, List.singleton_append] at ht
        simp [Dialect.hash, Dialect.hashWord, ht]
  | exact q =>
      simp only [Dialect.text, Dialect.atomText]
      rw [step_numeral hL (numHead_ratText q) (fun x hx => bareChar_of_notDelim hL (by
        rcases ratText_chars q x hx with h | h | h <;> simp [h])) hrest, classify_ratText]
  | inexact d =>
      simp only [Dialect.text, Dialect.atomText]
      rw [step_numeral hL (numHead_decText d) (fun x hx => bareChar_of_notDelim hL (by
        rcases decText_chars d x hx with h | h | h <;> simp [h])) hrest, classify_decText]
  | char c =>
      simp only [Dialect.text, Dialect.atomText]
      have ht := takeToken_append (p := D.bareChar) (w := []) (rest := rest) (by simp) hnb
      rw [List.cons_append, List.cons_append, step_hash hL (by decide)]
      simp only [List.nil_append] at ht
      simp [Dialect.hash, Dialect.hashChar, ht]
  | string s =>
      simp only [Dialect.text, Dialect.atomText]
      have heq : '"' :: escapeQuoted '"' s.toList ++ ['"'] ++ rest =
          '"' :: (escapeQuoted '"' s.toList ++ '"' :: rest) := by simp
      rw [heq, step_quoted (Or.inl rfl)]
      have hr := readQuoted_escape (q := '"') hL.string_backslash hL.string_quote (by decide)
        s.toList rest
      simp [Dialect.dispatch, hL.opener_special.1, hL.closer_special.1, hr]
  | vector => simp [Dialect.role] at hrole
  | bytevector =>
      simp only [Dialect.role] at hrole
      split at hrole <;> cases hrole
  | box =>
      simp only [Dialect.role] at hrole
      split at hrole <;> cases hrole

theorem ratText_ne_nil (q : ℚ) : ratText q ≠ [] := by
  obtain ⟨c, r, h, -⟩ := numHead_ratText q; rw [h]; simp

theorem atomText_ne_nil (a : Atom) : D.atomText a ≠ [] := by
  cases a with
  | symbol s =>
      simp only [Dialect.atomText]
      split
      · rename_i hb
        intro h; rw [h] at hb; simp [Dialect.bareSymbol] at hb
      · simp
  | keyword s => simp only [Dialect.atomText]; split <;> simp
  | boolean b => simp only [Dialect.atomText]; split <;> simp
  | exact q => exact ratText_ne_nil q
  | inexact d => simp [Dialect.atomText, Decimal.text]
  | _ => simp [Dialect.atomText]

theorem printLaws (hL : D.Laws) : PrintLaws D.syntaxNotation D.lexer D.text where
  size_eq _ := rfl
  space s := by
    show D.step (' ' :: s) = D.step s
    simp only [Dialect.step, skip_ws (c := ' ') (by decide)]
  eof := by show D.step [] = .eof; simp [Dialect.step, skip]
  atom a rest h hf := step_atom hL a rest h hf
  dot _ rest hf := by
    have hrest := delimited_of_follows hL hf
    have hb : D.bareChar '.' = true := bareChar_of_notDelim hL (by simp)
    have ht := takeToken_append (p := D.bareChar) (w := ['.']) (by simp [hb])
      (not_bareChar_of_delimited hrest)
    have hhead : (rest.head? = some '|' || rest.head? = some '\\') = false := by
      cases rest with
      | nil => rfl
      | cons c r =>
          obtain ⟨-, h1, h2, -⟩ := hrest c r rfl
          simp [h1, h2]
    show D.step ('.' :: rest) = _
    rw [step_of_skip (skip_stop _ (not_whitespace_of_bareChar hL hb) (by decide) (by decide)),
      dispatch_bare hL _ hb (by decide) (by decide) (by decide) (by decide)]
    simp only [List.singleton_append] at ht
    simp [Dialect.bare, ht, hhead]
  openList rest := by
    show D.step ('(' :: rest) = _
    rw [step_of_skip (skip_stop _ (by decide) (by decide) (by decide))]
    simp [Dialect.dispatch, hL.opener_paren, Dialect.syntaxNotation]
  openColl m c d rest h := by
    change D.role m = .coll c d at h
    cases m with
    | vector =>
        simp only [Dialect.role, Role.coll.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show D.step ('#' :: '(' :: rest) = _
        rw [step_hash hL (by decide)]
        simp [Dialect.hash]
    | bytevector =>
        simp only [Dialect.role] at h
        split at h
        · rename_i hbv
          simp only [Role.coll.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          show D.step ('#' :: 'u' :: '8' :: '(' :: rest) = _
          rw [step_hash hL (by decide)]
          simp [Dialect.hash, hbv, Dialect.hashU8]
        · cases h
    | symbol => simp only [Dialect.role] at h; split at h <;> cases h
    | keyword => simp only [Dialect.role] at h; split at h <;> cases h
    | box => simp only [Dialect.role] at h; split at h <;> cases h
    | _ => simp [Dialect.role] at h
  close k rest := by
    show D.step (D.brackets.closeChar k :: rest) = _
    obtain ⟨-, -, h3, h4, h5⟩ := hL.closeChar_special k
    rw [step_of_skip (skip_stop _ h5 h3 h4)]
    simp [Dialect.dispatch, hL.opener_closeChar k, hL.closer_closeChar k]
  «prefix» p rest h := by
    change D.role p = .prefix at h
    cases p with
    | box =>
        simp only [Dialect.role] at h
        split at h
        · rename_i hbox
          show D.step ('#' :: '&' :: ' ' :: rest) = _
          rw [step_hash hL (by decide)]
          simp [Dialect.hash, hbox]
        · cases h
    | symbol => simp only [Dialect.role] at h; split at h <;> cases h
    | keyword => simp only [Dialect.role] at h; split at h <;> cases h
    | bytevector => simp only [Dialect.role] at h; split at h <;> cases h
    | _ => simp [Dialect.role] at h
  nonempty t := by
    cases t with
    | atom a => exact atomText_ne_nil a
    | «open» h c d => cases h <;> simp [Dialect.text, atomText_ne_nil]
    | «prefix» p => exact atomText_ne_nil p
    | _ => simp [Dialect.text]

/-! ## The lexer respects the encoding -/

theorem takeToken_all {p : Char → Bool} : ∀ {cs w r : List Char},
    takeToken p cs = (w, r) → ∀ x ∈ w, p x = true := by
  intro cs
  induction cs with
  | nil => intro w r h; simp [takeToken] at h; obtain ⟨rfl, -⟩ := h; simp
  | cons c cs ih =>
      intro w r h
      simp only [takeToken] at h
      split at h
      · rename_i hc
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hc
        · exact ih rfl x hx
      · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp

theorem symbol_ok {w : List Char} (hw : D.writableName w = true) :
    D.syntaxNotation.TokenOK (.atom (.symbol (String.ofList w))) := by
  simp [Notation.TokenOK, Dialect.syntaxNotation, Dialect.role, hw]

theorem quote_ok (hL : D.Laws) {s : String} (hs : s ∈ ["quote", "quasiquote", "unquote",
    "unquote-splicing", "syntax", "quasisyntax", "unsyntax", "unsyntax-splicing"]) :
    D.syntaxNotation.TokenOK (.prefix (.symbol s)) := by
  right
  simp [Dialect.syntaxNotation, Dialect.role, hL.quote_writable s hs]

theorem comma_ok (hL : D.Laws) {a b : String} {r s' : List Char} {t : Token Atom C}
    (ha : a ∈ ["quote", "quasiquote", "unquote", "unquote-splicing", "syntax", "quasisyntax",
      "unsyntax", "unsyntax-splicing"])
    (hb : b ∈ ["quote", "quasiquote", "unquote", "unquote-splicing", "syntax", "quasisyntax",
      "unsyntax", "unsyntax-splicing"])
    (h : (comma a b r : Step Atom C (List Char)) = .token t s') : D.syntaxNotation.TokenOK t := by
  cases r with
  | nil => simp only [comma, Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h; exact quote_ok hL ha
  | cons d r =>
      simp only [comma] at h
      split at h <;> simp only [Step.token.injEq] at h <;> obtain ⟨rfl, -⟩ := h
      · exact quote_ok hL hb
      · exact quote_ok hL ha

theorem bare_ok (hL : D.Laws) {cs s' : List Char} {t : Token Atom C}
    (h : D.bare cs = .token t s') : D.syntaxNotation.TokenOK t := by
  simp only [Dialect.bare] at h
  cases hwr : takeToken D.bareChar cs with
  | mk w r =>
  simp only [hwr] at h
  have hall := takeToken_all hwr
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h; trivial
  split at h
  · rename_i a hcls
    simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h
    simp only [Dialect.classify] at hcls
    split at hcls
    · split at hcls
      · cases hcls; rfl
      · split at hcls
        · cases hcls; rfl
        · cases hcls
    · split at hcls
      · cases hcls
        exact symbol_ok (by simpa using hL.bare_writable w (List.all_eq_true.2 hall))
      · cases hcls
  · cases h

theorem hash_ok (hL : D.Laws) {cs s' : List Char} {t : Token Atom C}
    (h : D.hash cs = .token t s') : D.syntaxNotation.TokenOK t := by
  cases cs with
  | nil => cases h
  | cons c r =>
      simp only [Dialect.hash] at h
      split at h
      · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
      split at h
      · -- characters
        cases r with
        | nil => cases h
        | cons ch r =>
            simp only [Dialect.hashChar] at h
            cases hwr : takeToken D.bareChar r with
            | mk w r' =>
            simp only [hwr] at h
            split at h
            · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
            · split at h
              · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
              · cases h
      split at h
      · -- bytevectors
        rename_i hu
        simp only [Bool.and_eq_true] at hu
        simp only [Dialect.hashU8] at h
        split at h
        · split at h
          · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h
            simp [Notation.TokenOK, Dialect.syntaxNotation, Dialect.role, hu.2]
          · cases h
        · cases h
      split at h
      · -- keywords
        rename_i hk
        simp only [Bool.and_eq_true] at hk
        cases r with
        | nil => cases h
        | cons d r =>
            simp only [Dialect.hashKeyword] at h
            split at h
            · split at h
              · rename_i w r' hq
                simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h
                simp [Notation.TokenOK, Dialect.syntaxNotation, Dialect.role, hk.2,
                  hL.bar_writable _ _ _ hq]
              · cases h
            · simp only [Dialect.keywordWord] at h
              cases hwr : takeToken D.bareChar (d :: r) with
              | mk w r' =>
              simp only [hwr] at h
              split at h
              · cases h
              · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h
                simp [Notation.TokenOK, Dialect.syntaxNotation, Dialect.role, hk.2,
                  hL.bare_writable w (List.all_eq_true.2 (takeToken_all hwr))]
      split at h
      · rename_i hb
        simp only [Bool.and_eq_true] at hb
        simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h
        left; simp [Dialect.syntaxNotation, Dialect.role, hb.2]
      split at h
      · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h; exact quote_ok hL (by simp)
      split at h
      · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h; exact quote_ok hL (by simp)
      split at h
      · exact comma_ok hL (by simp) (by simp) h
      · simp only [Dialect.hashWord] at h
        cases hwr : takeToken D.bareChar (c :: r) with
        | mk w r' =>
        simp only [hwr] at h
        split at h
        · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
        split at h
        · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
        · cases h

theorem step_ok (hL : D.Laws) (s : List Char) (t : Token Atom C) (s' : List Char)
    (h : D.step s = .token t s') : D.syntaxNotation.TokenOK t := by
  simp only [Dialect.step] at h
  split at h
  · cases h
  · cases h
  rename_i c r _
  simp only [Dialect.dispatch] at h
  split at h
  · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h
    intro _; rfl
  split at h
  · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h; trivial
  split at h
  · split at h
    · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
    · cases h
  split at h
  · split at h
    · rename_i w r' hq
      simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact symbol_ok (by simpa using hL.bar_writable _ _ _ hq)
    · cases h
  split at h
  · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h; exact quote_ok hL (by simp)
  split at h
  · simp only [Step.token.injEq] at h; obtain ⟨rfl, -⟩ := h; exact quote_ok hL (by simp)
  split at h
  · exact comma_ok hL (by simp) (by simp) h
  split at h
  · exact hash_ok hL h
  · exact bare_ok hL h

end Silmaril.Proofs.Formats.SExp.SchemeFamily
