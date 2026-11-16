module

public import Silmaril.Formats.SExp.CommonLisp.Defs
import Silmaril.Proofs.Formats.SExp.Lexical.Basic

/-! # Proofs: the Common Lisp reader lexes its printed tokens back -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.CommonLisp

open Silmaril.Formats Silmaril.Formats.SExpReader Silmaril.Formats.SExpLexical
open Silmaril.Formats.CommonLisp
open Silmaril.Proofs.Formats.SExp.Lexical

/-! ## Atmosphere -/

theorem skip_white {c : Char} (h : isWhite c = true) (s : List Char) : skip (c :: s) = skip s := by
  simp [skip, h]

theorem skip_head {c : Char} (r : List Char) (hw : isWhite c = false) (hs : c ≠ ';')
    (hh : c ≠ '#') : skip (c :: r) = some (c :: r) := by
  simp [skip, hw, hs, hh]

theorem skip_hash {d : Char} (r : List Char) (hd : d ≠ '|') :
    skip ('#' :: d :: r) = some ('#' :: d :: r) := by
  simp [skip, isWhite, skipHash, hd]

theorem step_of_skip {s r : List Char} {c : Char} (h : skip s = some (c :: r)) :
    step s = dispatch c r := by
  simp [step, h]

/-! ## Follows -/

theorem follows_cases {rest : List Char} (h : Follows text rest) :
    rest = [] ∨ (∃ r, rest = ' ' :: r) ∨ (∃ r, rest = ')' :: r) := by
  rcases h with h | h | ⟨_, r, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨r, by simpa [text] using h⟩)

theorem follows_term {rest : List Char} (h : Follows text rest) :
    ∀ c r, rest = c :: r → terminates c = true := by
  rintro c r rfl
  rcases follows_cases h with h | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h <;> decide

theorem tokNormal_follows {rest : List Char} (h : Follows text rest) :
    tokNormal rest = some ([], rest) := by
  rcases follows_cases h with rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · simp [tokNormal]
  · simp [tokNormal, terminates, isWhite]
  · simp [tokNormal, terminates]

/-! ## Tokens -/

theorem tokNormal_bare {cs : List Char} (rest : List Char)
    (hcs : ∀ c ∈ cs, c ≠ '\\' ∧ c ≠ '|' ∧ terminates c = false) :
    tokNormal (cs ++ rest) = (tokNormal rest).map (prepend (cs.map (Piece.ch · false))) := by
  induction cs with
  | nil =>
      simp only [List.nil_append, List.map_nil]
      cases tokNormal rest <;> simp [prepend]
  | cons c cs ih =>
      obtain ⟨h1, h2, h3⟩ := hcs c (by simp)
      simp only [List.cons_append, tokNormal, h1, h2, h3, ite_false, Bool.false_eq_true]
      rw [ih (fun d hd => hcs d (by simp [hd]))]
      cases tokNormal rest <;> simp [prepend]

theorem tokBar_escape (cs rest : List Char) :
    tokBar (escapeQuoted '|' cs ++ '|' :: rest) =
      (tokNormal rest).map (prepend (cs.map (Piece.ch · true) ++ [.bar])) := by
  induction cs with
  | nil =>
      simp only [escapeQuoted, List.nil_append, tokBar]
      cases tokNormal rest <;> simp [prepend]
  | cons c cs ih =>
      by_cases hc : c = '|' ∨ c = '\\'
      · simp only [escapeQuoted]
        rw [ite_eq_left (by simpa using hc)]
        simp only [List.cons_append, List.nil_append, tokBar, ite_true, tokEscB]
        rw [ih]
        cases tokNormal rest <;> simp [prepend]
      · simp only [not_or] at hc
        simp only [escapeQuoted]
        rw [ite_eq_right (by simp [hc.1, hc.2])]
        simp only [List.cons_append, List.nil_append, tokBar, hc.1, hc.2, ite_false]
        rw [ih]
        cases tokNormal rest <;> simp [prepend]

/-- The pieces a printed name reads as. -/
def namePieces (s : String) : List Piece :=
  if bareName s.toList then s.toList.map (Piece.ch · false)
  else .bar :: s.toList.map (Piece.ch · true) ++ [.bar]

theorem safeChar_spec {c : Char} (h : safeChar c = true) :
    c ≠ '\\' ∧ c ≠ '|' ∧ terminates c = false ∧ c ≠ ':' ∧ c ≠ '#' ∧ invalidChar c = false ∧
      c.toUpper = c := by
  simp only [safeChar, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h3, h2, h1, h4, h5, h6, h7⟩

theorem bareName_spec {cs : List Char} (h : bareName cs = true) :
    cs ≠ [] ∧ (∀ c ∈ cs, safeChar c = true) ∧ cs.all (· = '.') = false ∧ number? cs = none ∧
      potNum cs = false := by
  simp only [bareName, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, Option.isNone_iff_eq_none, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem tokNormal_name (s : String) (rest : List Char) :
    tokNormal (nameText s ++ rest) = (tokNormal rest).map (prepend (namePieces s)) := by
  unfold nameText namePieces
  split
  · rename_i hb
    obtain ⟨-, hsafe, -⟩ := bareName_spec hb
    exact tokNormal_bare rest fun c hc =>
      let h := safeChar_spec (hsafe c hc); ⟨h.1, h.2.1, h.2.2.1⟩
  · simp only [List.cons_append, List.append_assoc, tokNormal]
    simp only [show ('|' = '\\') = False by decide, ite_false, ite_true]
    rw [tokBar_escape]
    cases h : tokNormal rest <;> simp [prepend, h]

theorem namePieces_ne_nil (s : String) : namePieces s ≠ [] := by
  unfold namePieces; split
  · rename_i hb; simpa using (bareName_spec hb).1
  · simp

theorem namePieces_noColon (s : String) : ∀ p ∈ namePieces s, p.isColon = false := by
  unfold namePieces; split
  · rename_i hb
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    have := (safeChar_spec ((bareName_spec hb).2.1 c hc)).2.2.2.1
    simp [Piece.isColon, this]
  · intro p hp
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hp
    rcases hp with (rfl | ⟨c, -, rfl⟩) | rfl <;> simp [Piece.isColon]

theorem folded_false {cs : List Char} (h : ∀ c ∈ cs, c.toUpper = c) :
    (cs.map (Piece.ch · false)).filterMap Piece.folded = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp [Piece.folded, h c (by simp), ih (fun d hd => h d (by simp [hd]))]

theorem folded_true (cs : List Char) :
    (cs.map (Piece.ch · true)).filterMap Piece.folded = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [Piece.folded, ih]

theorem name_namePieces (s : String) : name (namePieces s) = s := by
  unfold namePieces name; split
  · rename_i hb
    have hsafe := (bareName_spec hb).2.1
    rw [folded_false (fun c hc => (safeChar_spec (hsafe c hc)).2.2.2.2.2.2),
      String.ofList_toList]
  · simp only [List.filterMap_cons, Piece.folded, List.filterMap_append, folded_true,
      List.filterMap_nil, List.append_nil]
    exact String.ofList_toList

theorem namePieces_valid (s : String) :
    ((namePieces s).filterMap Piece.unescaped).any invalidChar = false := by
  unfold namePieces; split
  · rename_i hb
    have hsafe := (bareName_spec hb).2.1
    simp only [List.any_eq_false]
    intro c hc
    simp only [List.mem_filterMap, List.mem_map] at hc
    obtain ⟨p, ⟨d, hd, rfl⟩, hp⟩ := hc
    simp only [Piece.unescaped, Option.some.injEq] at hp
    subst hp
    simp [(safeChar_spec (hsafe d hd)).2.2.2.2.2.1]
  · simp [Piece.unescaped, Function.comp_def]

/-! ## Splitting at colons -/

theorem splitColon_ne_nil (ys : List Piece) : splitColon ys ≠ [] := by
  cases ys with
  | nil => simp [splitColon]
  | cons p r =>
      simp only [splitColon]
      split
      · simp
      · split <;> simp

theorem splitColon_free {xs : List Piece} (h : ∀ p ∈ xs, p.isColon = false) (ys : List Piece) :
    splitColon (xs ++ ys) =
      match splitColon ys with
      | s :: ss => (xs ++ s) :: ss
      | [] => [xs] := by
  induction xs with
  | nil =>
      simp only [List.nil_append]
      cases hs : splitColon ys with
      | nil => exact absurd hs (splitColon_ne_nil ys)
      | cons => rfl
  | cons p xs ih =>
      have hp := h p (by simp)
      simp only [List.cons_append, splitColon, hp, Bool.false_eq_true, ite_false]
      rw [ih (fun q hq => h q (by simp [hq]))]
      cases splitColon ys <;> rfl

theorem splitColon_single {xs : List Piece} (h : ∀ p ∈ xs, p.isColon = false) :
    splitColon xs = [xs] := by
  have := splitColon_free h []
  simpa [splitColon] using this

theorem splitColon_colon (ys : List Piece) :
    splitColon (.ch ':' false :: ys) = [] :: splitColon ys := by
  simp [splitColon, Piece.isColon]

/-! ## Dispatch to the token reader -/

theorem step_chunk {cs rest : List Char} {ps : List Piece} {c : Char} {r : List Char}
    (hcs : cs = c :: r) (ht : terminates c = false) (hh : c ≠ '#')
    (htok : tokNormal (cs ++ rest) = some (ps, rest)) :
    step (cs ++ rest) = ofToken (classify ps) rest := by
  subst hcs
  have hw : isWhite c = false := by
    simp only [terminates, Bool.or_eq_false_iff] at ht; exact ht.1.1.1.1.1.1.1
  simp only [terminates, Bool.or_eq_false_iff, decide_eq_false_iff_not] at ht
  obtain ⟨⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := ht
  rw [List.cons_append] at htok ⊢
  rw [step_of_skip (skip_head _ hw h5 hh)]
  simp only [dispatch, h1, h2, h3, h4, h6, h7, hh, ite_false, htok]

theorem digit_props {c : Char} (h : c.isDigit = true) :
    terminates c = false ∧ c ≠ '\\' ∧ c ≠ '|' ∧ c ≠ '.' ∧ c ≠ ':' ∧ invalidChar c = false ∧
      c ≠ '#' := by
  have key : ∀ d : Char, d.isDigit = false → c ≠ d := by rintro d hd rfl; simp [hd] at h
  refine ⟨?_, key _ (by decide), key _ (by decide), key _ (by decide), key _ (by decide), ?_,
    key _ (by decide)⟩
  · simp only [terminates, isWhite, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    repeat' constructor
    all_goals exact key _ (by decide)
  · simp only [invalidChar, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨key _ (by decide), key _ (by decide)⟩

/-! ## Classification -/

theorem unescaped_false (cs : List Char) :
    (cs.map (Piece.ch · false)).filterMap Piece.unescaped = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [Piece.unescaped, ih]

theorem noEscape_false (cs : List Char) : (cs.map (Piece.ch · false)).any Piece.isEscape = false := by
  simp [Piece.isEscape]

theorem symbolic_single {ps : List Piece} (h : ∀ p ∈ ps, p.isColon = false) :
    symbolic ps = some (.atom (.symbol (name ps))) := by
  simp [symbolic, splitColon_single h]

theorem classify_namePieces (s : String) :
    classify (namePieces s) = some (.atom (.symbol s)) := by
  have hv := namePieces_valid s
  have hsym : symbolic (namePieces s) = some (.atom (.symbol s)) := by
    rw [symbolic_single (namePieces_noColon s), name_namePieces]
  unfold classify
  rw [ite_eq_right (by rw [hv]; decide)]
  unfold namePieces at hsym ⊢
  split
  · rename_i hb
    obtain ⟨-, hsafe, hdots, hnum, hpot⟩ := bareName_spec hb
    have hcolon : s.toList.contains ':' = false := by
      simp only [List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq]
      intro c hc h; exact (safeChar_spec (hsafe c hc)).2.2.2.1 h.symm
    rw [ite_eq_right (by rw [noEscape_false]; decide)]
    dsimp only
    rw [unescaped_false, ite_eq_right (by rw [hdots]; decide),
      ite_eq_right (by rw [hcolon]; decide), hnum]
    dsimp only
    rw [ite_eq_right (by rw [hpot]; decide)]
    rw [ite_eq_left hb] at hsym
    exact hsym
  · rename_i hb
    rw [ite_eq_right hb] at hsym
    rw [ite_eq_left (by simp [Piece.isEscape])]
    exact hsym

/-- Classification of a token with an escape or an unescaped colon is by package markers. -/
theorem classify_symbolic {ps : List Piece}
    (hv : (ps.filterMap Piece.unescaped).any invalidChar = false)
    (h : ps.any Piece.isEscape = true ∨ (ps.filterMap Piece.unescaped).contains ':' = true) :
    classify ps = symbolic ps := by
  unfold classify
  rw [ite_eq_right (by rw [hv]; decide)]
  by_cases he : ps.any Piece.isEscape = true
  · rw [ite_eq_left he]
  · rw [ite_eq_right he]
    have hc : (ps.filterMap Piece.unescaped).contains ':' = true := by
      rcases h with h | h
      · exact absurd h he
      · exact h
    have hd : (ps.filterMap Piece.unescaped).all (· = '.') = false := by
      simp only [List.contains_eq_any_beq, List.any_eq_true, beq_iff_eq] at hc
      obtain ⟨c, hc, rfl⟩ := hc
      simp only [List.all_eq_false]
      exact ⟨':', hc, by decide⟩
    dsimp only
    rw [ite_eq_right (by rw [hd]; decide), ite_eq_left hc]

theorem namePieces_escape_or_chars (s : String) :
    (namePieces s).any Piece.isEscape = true ∨
      (namePieces s = s.toList.map (Piece.ch · false)) := by
  unfold namePieces; split
  · exact Or.inr rfl
  · exact Or.inl (by simp [Piece.isEscape])

theorem any_escape_append {xs ys : List Piece} :
    (xs ++ ys).any Piece.isEscape = (xs.any Piece.isEscape || ys.any Piece.isEscape) := by
  simp [List.any_append]

/-! ## Character classes of printed numerals -/

theorem ratText_chars (q : ℚ) : ∀ c ∈ ratText q, c.isDigit = true ∨ c = '-' ∨ c = '/' := by
  intro c hc
  unfold ratText at hc
  split at hc
  · rcases intText_chars _ c hc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · simp only [List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | hc
    · rcases intText_chars _ c hc with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl (natText_isDigit _ c hc)

theorem intText_digit (n : Int) : ∃ c ∈ intText n, c.isDigit = true := by
  unfold intText
  split
  · obtain ⟨c, r, hcr, hd⟩ := natText_head n.natAbs
    exact ⟨c, by simp [hcr], hd⟩
  · obtain ⟨c, r, hcr, hd⟩ := natText_head n.toNat
    exact ⟨c, by simp [hcr], hd⟩

theorem ratText_digit (q : ℚ) : ∃ c ∈ ratText q, c.isDigit = true := by
  obtain ⟨c, hc, hd⟩ := intText_digit q.num
  refine ⟨c, ?_, hd⟩
  unfold ratText; split
  · exact hc
  · simp [hc]

theorem decText_chars (f : FloatFormat) (d : Decimal) :
    ∀ c ∈ Decimal.text f.marker d, c.isDigit = true ∨ c = '-' ∨ c = f.marker := by
  intro c hc
  simp only [Decimal.text, List.mem_append, List.mem_cons] at hc
  rcases hc with (hc | hc) | rfl | hc
  · split at hc <;> simp_all
  · exact Or.inl (natText_isDigit _ c hc)
  · exact Or.inr (Or.inr rfl)
  · rcases intText_chars _ c hc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem marker_spec (f : FloatFormat) :
    isMarker f.marker = true ∧ f.marker.isDigit = false ∧ f.marker ≠ '.' ∧
      fmtOf (some f.marker) = f ∧ terminates f.marker = false ∧ f.marker ≠ '\\' ∧
      f.marker ≠ '|' ∧ f.marker ≠ ':' ∧ f.marker ≠ '/' ∧ invalidChar f.marker = false := by
  cases f <;> decide

theorem digits?_none {cs : List Char} (h : ∃ c ∈ cs, c.isDigit = false) : digits? cs = none := by
  obtain ⟨c, hc, hd⟩ := h
  have : cs.all Char.isDigit = false := List.all_eq_false.2 ⟨c, hc, by simp [hd]⟩
  simp [digits?, this]

theorem number?_decText (f : FloatFormat) (d : Decimal) :
    number? (Decimal.text f.marker d) = some (.float d f) := by
  obtain ⟨hm, hmd, hmp, hfmt, -, -, -, -, hms, -⟩ := marker_spec f
  have hchars := decText_chars f d
  have hmem : f.marker ∈ Decimal.text f.marker d := by simp [Decimal.text]
  have hslash : takeToken (fun c => c != '/') (Decimal.text f.marker d) =
      (Decimal.text f.marker d, []) := by
    have := takeToken_append (p := fun c => c != '/') (w := Decimal.text f.marker d) (rest := [])
      (fun c hc => by
        rcases hchars c hc with h | rfl | rfl
        · have : c ≠ '/' := by rintro rfl; simp [Char.isDigit] at h
          simpa using this
        · decide
        · simpa using hms)
      (by simp)
    simpa using this
  have hdot : takeToken (fun c => c != '.') (Decimal.text f.marker d) =
      (Decimal.text f.marker d, []) := by
    have := takeToken_append (p := fun c => c != '.') (w := Decimal.text f.marker d) (rest := [])
      (fun c hc => by
        rcases hchars c hc with h | rfl | rfl
        · have : c ≠ '.' := by rintro rfl; simp [Char.isDigit] at h
          simpa using this
        · decide
        · simpa using hmp)
      (by simp)
    simpa using this
  have hint : int? (Decimal.text f.marker d) = none := by
    obtain ⟨neg, sig, ex⟩ := d
    obtain ⟨c, r, hcr, hcd⟩ := natText_head sig
    have hs := not_sign_of_isDigit hcd
    have hnd : digits? (natText sig ++ f.marker :: intText ex) = none :=
      digits?_none ⟨f.marker, by simp, hmd⟩
    cases neg
    · simp only [Decimal.text, Bool.false_eq_true, ite_false, List.nil_append]
      rw [hcr] at hnd ⊢
      simp only [List.cons_append] at hnd ⊢
      simp [int?, hs.1, hs.2, hnd]
    · simp [Decimal.text, int?, hnd]
  have hrat : rational? (Decimal.text f.marker d) = none := by
    simp [rational?, hslash, hint]
  have htd : trailingDotInt? (Decimal.text f.marker d) = none := by
    simp [trailingDotInt?, hdot]
  simp [number?, hrat, htd, readDecimal_text hm hmd hmp, hfmt]

theorem number?_ratText (q : ℚ) : number? (ratText q) = some (.rational q) := by
  simp [number?, rational?_ratText]

/-- A numeral token: no escapes, classified as the given number. -/
theorem classify_numeral {cs : List Char} {a : Atom}
    (hchars : ∀ c ∈ cs, c.isDigit = true ∨ c = '-' ∨ c = '/' ∨ c ∈ ['e', 's', 'f', 'd', 'l'])
    (hdigit : ∃ c ∈ cs, c.isDigit = true) (hnum : number? cs = some a) :
    classify (cs.map (Piece.ch · false)) = some (.atom a) := by
  have hv : cs.any invalidChar = false := by
    simp only [List.any_eq_false]
    intro c hc
    rcases hchars c hc with h | rfl | rfl | h
    · simp [(digit_props h).2.2.2.2.2.1]
    · decide
    · decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> decide
  have hd : cs.all (· = '.') = false := by
    obtain ⟨c, hc, hd⟩ := hdigit
    simp only [List.all_eq_false]
    refine ⟨c, hc, ?_⟩
    simpa using (digit_props hd).2.2.2.1
  have hcolon : cs.contains ':' = false := by
    simp only [List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq]
    intro c hc h
    subst h
    rcases hchars ':' hc with h | h | h | h
    · exact absurd rfl (digit_props h).2.2.2.2.1
    · cases h
    · cases h
    · simp at h
  unfold classify
  rw [unescaped_false, ite_eq_right (by rw [hv]; decide),
    ite_eq_right (by rw [noEscape_false]; decide)]
  dsimp only
  rw [ite_eq_right (by rw [hd]; decide),
    ite_eq_right (by rw [hcolon]; decide), hnum]

/-! ## Lexing laws of atoms -/

theorem tokNormal_numeral {cs rest : List Char} (hrest : Follows text rest)
    (hchars : ∀ c ∈ cs, c.isDigit = true ∨ c = '-' ∨ c = '/' ∨ c ∈ ['e', 's', 'f', 'd', 'l']) :
    tokNormal (cs ++ rest) = some (cs.map (Piece.ch · false), rest) := by
  rw [tokNormal_bare rest, tokNormal_follows hrest]
  · simp [prepend]
  · intro c hc
    rcases hchars c hc with h | rfl | rfl | h
    · have := digit_props h
      exact ⟨this.2.1, this.2.2.1, this.1⟩
    · decide
    · decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Heads of printed atoms -/

theorem nameText_head (s : String) :
    ∃ c r, nameText s = c :: r ∧ terminates c = false ∧ c ≠ '#' := by
  unfold nameText
  split
  · rename_i hb
    obtain ⟨hne, hsafe, -⟩ := bareName_spec hb
    cases h : s.toList with
    | nil => exact absurd h hne
    | cons c r =>
        have := safeChar_spec (hsafe c (by simp [h]))
        exact ⟨c, r, rfl, this.2.2.1, this.2.2.2.2.1⟩
  · exact ⟨'|', _, rfl, by decide, by decide⟩

theorem intText_head (n : Int) : ∃ c r, intText n = c :: r ∧ (c.isDigit = true ∨ c = '-') := by
  unfold intText
  split
  · exact ⟨'-', _, rfl, Or.inr rfl⟩
  · obtain ⟨c, r, hcr, hd⟩ := natText_head n.toNat
    exact ⟨c, r, hcr, Or.inl hd⟩

theorem head_ok {c : Char} (h : c.isDigit = true ∨ c = '-') : terminates c = false ∧ c ≠ '#' := by
  rcases h with h | rfl
  · exact ⟨(digit_props h).1, (digit_props h).2.2.2.2.2.2⟩
  · decide

theorem ratText_head (q : ℚ) : ∃ c r, ratText q = c :: r ∧ terminates c = false ∧ c ≠ '#' := by
  obtain ⟨c, r, hcr, hc⟩ := intText_head q.num
  refine ⟨c, ?_, ?_, head_ok hc⟩
  · exact if q.den = 1 then r else r ++ '/' :: natText q.den
  · unfold ratText; split <;> simp [*]

theorem decText_head (f : FloatFormat) (d : Decimal) :
    ∃ c r, Decimal.text f.marker d = c :: r ∧ terminates c = false ∧ c ≠ '#' := by
  obtain ⟨neg, sig, ex⟩ := d
  cases neg
  · obtain ⟨c, r, hcr, hd⟩ := natText_head sig
    exact ⟨c, r ++ f.marker :: intText ex, by simp [Decimal.text, hcr], head_ok (Or.inl hd)⟩
  · exact ⟨'-', _, rfl, by decide⟩

theorem numeral_chars_rat (q : ℚ) :
    ∀ c ∈ ratText q, c.isDigit = true ∨ c = '-' ∨ c = '/' ∨ c ∈ ['e', 's', 'f', 'd', 'l'] := by
  intro c hc
  rcases ratText_chars q c hc with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem numeral_chars_dec (f : FloatFormat) (d : Decimal) :
    ∀ c ∈ Decimal.text f.marker d,
      c.isDigit = true ∨ c = '-' ∨ c = '/' ∨ c ∈ ['e', 's', 'f', 'd', 'l'] := by
  intro c hc
  rcases decText_chars f d c hc with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · subst h; cases f <;> simp [FloatFormat.marker]

theorem decText_digit (f : FloatFormat) (d : Decimal) :
    ∃ c ∈ Decimal.text f.marker d, c.isDigit = true := by
  obtain ⟨c, r, hcr, hd⟩ := natText_head d.significand
  exact ⟨c, by simp [Decimal.text, hcr], hd⟩

/-! ## Lexing laws -/

theorem tokNormal_nameText (s : String) {rest : List Char} (hrest : Follows text rest) :
    tokNormal (nameText s ++ rest) = some (namePieces s, rest) := by
  rw [tokNormal_name, tokNormal_follows hrest]; simp [prepend]

theorem noInvalid_append {xs ys : List Piece}
    (hx : (xs.filterMap Piece.unescaped).any invalidChar = false)
    (hy : (ys.filterMap Piece.unescaped).any invalidChar = false) :
    ((xs ++ ys).filterMap Piece.unescaped).any invalidChar = false := by
  simp only [List.filterMap_append, List.any_append, hx, hy, Bool.or_false]

theorem colon_valid : ([Piece.ch ':' false].filterMap Piece.unescaped).any invalidChar = false := by
  decide

def colonChars (i : Bool) : List Char := if i then [':', ':'] else [':']
def colonPieces (i : Bool) : List Piece :=
  if i then [.ch ':' false, .ch ':' false] else [.ch ':' false]

theorem step_atom (a : Atom) (hrole : role a = .plain) (rest : List Char)
    (hrest : Follows text rest) : step (text (.atom a) ++ rest) = .token (.atom a) rest := by
  cases a with
  | symbol s =>
      obtain ⟨c, r, hcr, ht, hh⟩ := nameText_head s
      rw [show text (.atom (.symbol s)) = nameText s from rfl,
        step_chunk hcr ht hh (tokNormal_nameText s hrest), classify_namePieces]
      rfl
  | keyword s =>
      have htok : tokNormal (text (.atom (.keyword s)) ++ rest) =
          some (.ch ':' false :: namePieces s, rest) := by
        simp only [text, atomText, List.cons_append]
        rw [show ':' :: (nameText s ++ rest) = [':'] ++ (nameText s ++ rest) from rfl,
          tokNormal_bare _ (by decide), tokNormal_nameText s hrest]
        simp [prepend]
      rw [step_chunk (cs := text (.atom (.keyword s))) rfl (by decide) (by decide) htok]
      have hcl := classify_symbolic (ps := .ch ':' false :: namePieces s)
        (noInvalid_append (xs := [.ch ':' false]) colon_valid (namePieces_valid s))
        (Or.inr (by simp [Piece.unescaped]))
      rw [hcl]
      simp [symbolic, splitColon_colon, splitColon_single (namePieces_noColon s),
        namePieces_ne_nil, name_namePieces, ofToken]
  | qualified p s i =>
      obtain ⟨c, r, hcr, ht, hh⟩ := nameText_head p
      have hcols : tokNormal (colonChars i ++ (nameText s ++ rest)) =
          some (colonPieces i ++ namePieces s, rest) := by
        have := tokNormal_bare (cs := colonChars i) (nameText s ++ rest)
          (by intro c hc; cases i <;> simp [colonChars] at hc <;> subst hc <;> decide)
        rw [this, tokNormal_nameText s hrest]
        cases i <;> simp [prepend, colonChars, colonPieces]
      have htok : tokNormal (text (.atom (.qualified p s i)) ++ rest) =
          some (namePieces p ++ (colonPieces i ++ namePieces s), rest) := by
        simp only [text, atomText, List.append_assoc]
        rw [tokNormal_name, show (if i then [':', ':'] else [':']) = colonChars i from rfl, hcols]
        simp [prepend]
      have hcs : text (.atom (.qualified p s i)) = c :: (r ++ (colonChars i ++ nameText s)) := by
        simp [text, atomText, hcr, colonChars]
      rw [step_chunk hcs ht hh htok]
      have hvc : ((colonPieces i).filterMap Piece.unescaped).any invalidChar = false := by
        cases i <;> decide
      have hcl := classify_symbolic (ps := namePieces p ++ (colonPieces i ++ namePieces s))
        (noInvalid_append (namePieces_valid p) (noInvalid_append hvc (namePieces_valid s)))
        (Or.inr (by cases i <;> simp [colonPieces, List.filterMap_append, Piece.unescaped]))
      have hnp := namePieces_noColon p
      have hsplit : splitColon (namePieces p ++ (colonPieces i ++ namePieces s)) =
          if i then [namePieces p, [], namePieces s] else [namePieces p, namePieces s] := by
        rw [splitColon_free hnp]
        cases i <;> simp [colonPieces, splitColon_colon, splitColon_single (namePieces_noColon s)]
      rw [hcl, symbolic, hsplit]
      cases i <;> simp [namePieces_ne_nil, name_namePieces, ofToken]
  | uninterned s =>
      simp only [text, atomText, List.cons_append]
      rw [step_of_skip (skip_hash _ (by decide))]
      have hlen : (splitColon (namePieces s)).length = 1 := by
        rw [splitColon_single (namePieces_noColon s)]; rfl
      have hv := namePieces_valid s
      simp [dispatch, hashDispatch, tokNormal_nameText s hrest, namePieces_ne_nil, hlen,
        name_namePieces]
      simpa using hv
  | rational q =>
      obtain ⟨c, r, hcr, ht, hh⟩ := ratText_head q
      rw [show text (.atom (.rational q)) = ratText q from rfl,
        step_chunk hcr ht hh (tokNormal_numeral hrest (numeral_chars_rat q)),
        classify_numeral (numeral_chars_rat q) (ratText_digit q) (number?_ratText q)]
      rfl
  | float d f =>
      obtain ⟨c, r, hcr, ht, hh⟩ := decText_head f d
      rw [show text (.atom (.float d f)) = Decimal.text f.marker d from rfl,
        step_chunk hcr ht hh (tokNormal_numeral hrest (numeral_chars_dec f d)),
        classify_numeral (numeral_chars_dec f d) (decText_digit f d) (number?_decText f d)]
      rfl
  | string s =>
      have hr := readQuoted_escape (q := '"') (esc := some) rfl rfl (by decide) s.toList rest
      simp only [text, atomText, List.cons_append, List.append_assoc]
      rw [step_of_skip (skip_head _ (by decide) (by decide) (by decide))]
      simp [dispatch, hr, String.ofList_toList]
  | character c =>
      have htake : takeToken (fun c => !terminates c) rest = ([], rest) := by
        have := takeToken_append (p := fun c => !terminates c) (w := []) (rest := rest) (by simp)
          (by intro c r h; simp [follows_term hrest c r h])
        simpa using this
      simp only [text, atomText, List.cons_append, List.nil_append]
      rw [step_of_skip (skip_hash _ (by decide))]
      simp [dispatch, hashDispatch, htake]
  | vector => simp [role] at hrole
  | backquote => simp [role] at hrole
  | comma => simp [role] at hrole
  | commaAt => simp [role] at hrole

theorem step_space (s : List Char) : step (' ' :: s) = step s := by
  unfold step; rw [skip_white (by decide)]

theorem step_dot (rest : List Char) (hrest : Follows text rest) :
    step (text .dot ++ rest) = .token .dot rest := by
  have htok : tokNormal (['.'] ++ rest) = some ([.ch '.' false], rest) := by
    rw [tokNormal_bare rest (by decide), tokNormal_follows hrest]; simp [prepend]
  rw [show text (.dot : Token Atom Unit) = ['.'] from rfl,
    step_chunk (cs := ['.']) rfl (by decide) (by decide) htok]
  rfl

theorem atomText_ne_nil (a : Atom) : atomText a ≠ [] := by
  cases a with
  | symbol s => obtain ⟨c, r, h, -⟩ := nameText_head s; simp [atomText, h]
  | qualified p s i => obtain ⟨c, r, h, -⟩ := nameText_head p; simp [atomText, h]
  | rational q => obtain ⟨c, r, h, -⟩ := ratText_head q; simp [atomText, h]
  | float d f => obtain ⟨c, r, h, -⟩ := decText_head f d; simp [atomText, h]
  | _ => simp [atomText]

theorem text_ne_nil (t : Token Atom Unit) : text t ≠ [] := by
  cases t with
  | atom a => exact atomText_ne_nil a
  | «open» h c d =>
      cases h with
      | none => simp [text]
      | some m => exact atomText_ne_nil m
  | «prefix» p => exact atomText_ne_nil p
  | _ => simp [text]

theorem printLaws : PrintLaws syntaxNotation lexer text where
  size_eq _ := rfl
  space := step_space
  eof := rfl
  atom a rest h hr := step_atom a h rest hr
  dot _ rest hr := step_dot rest hr
  openList rest := by
    show step ('(' :: rest) = _
    rw [step_of_skip (skip_head _ (by decide) (by decide) (by decide))]
    simp [dispatch, syntaxNotation]
  openColl m c d rest h := by
    cases m <;> simp [syntaxNotation, role] at h
    obtain ⟨rfl, rfl⟩ := h
    show step ('#' :: '(' :: rest) = _
    rw [step_of_skip (skip_hash _ (by decide))]
    simp [dispatch, hashDispatch]
  close c rest := by
    show step (')' :: rest) = _
    rw [step_of_skip (skip_head _ (by decide) (by decide) (by decide))]
    simp [dispatch]
  «prefix» p rest h := by
    cases p <;> simp [syntaxNotation, role] at h
    · show step ('`' :: ' ' :: rest) = _
      rw [step_of_skip (skip_head _ (by decide) (by decide) (by decide))]
      simp [dispatch]
    · show step (',' :: ' ' :: rest) = _
      rw [step_of_skip (skip_head _ (by decide) (by decide) (by decide))]
      simp [dispatch]
    · show step (',' :: '@' :: ' ' :: rest) = _
      rw [step_of_skip (skip_head _ (by decide) (by decide) (by decide))]
      simp [dispatch]
  nonempty := text_ne_nil

/-! ## The lexer respects the notation -/

theorem symbolic_ok {ps : List Piece} {t : Token Atom Unit} (h : symbolic ps = some t) :
    syntaxNotation.TokenOK t := by
  unfold symbolic at h
  split at h <;> (try split_ifs at h) <;> cases h <;> rfl

theorem number?_plain {cs : List Char} {a : Atom} (h : number? cs = some a) : role a = .plain := by
  unfold number? at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases h

theorem classify_ok {ps : List Piece} {t : Token Atom Unit} (h : classify ps = some t) :
    syntaxNotation.TokenOK t := by
  unfold classify at h
  by_cases h1 : (ps.filterMap Piece.unescaped).any invalidChar = true
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h
  by_cases h2 : ps.any Piece.isEscape = true
  · rw [ite_eq_left h2] at h; exact symbolic_ok h
  rw [ite_eq_right h2] at h
  dsimp only at h
  by_cases h3 : (ps.filterMap Piece.unescaped).all (· = '.') = true
  · rw [ite_eq_left h3] at h
    split_ifs at h
    cases h; trivial
  rw [ite_eq_right h3] at h
  by_cases h4 : (ps.filterMap Piece.unescaped).contains ':' = true
  · rw [ite_eq_left h4] at h; exact symbolic_ok h
  rw [ite_eq_right h4] at h
  split at h
  · cases h; exact number?_plain ‹_›
  · split_ifs at h; exact symbolic_ok h

theorem ofToken_eq {o : Option (Token Atom Unit)} {r s' : List Char} {t : Token Atom Unit}
    (h : ofToken o r = .token t s') : o = some t := by
  cases o with
  | none => cases h
  | some t' => simp only [ofToken, Step.token.injEq] at h; rw [h.1]

theorem hash_ok {r s' : List Char} {t : Token Atom Unit} (h : hashDispatch r = .token t s') :
    syntaxNotation.TokenOK t := by
  unfold hashDispatch at h
  split at h
  · cases h
  · split_ifs at h
    · cases h; rfl
    · cases h; exact Or.inr rfl
    · split at h
      · cases h
      · split at h
        · cases h; rfl
        · split at h
          · cases h; rfl
          · cases h
    · split at h
      · split_ifs at h; cases h; rfl
      · cases h

theorem step_ok {s s' : List Char} {t : Token Atom Unit} (h : step s = .token t s') :
    syntaxNotation.TokenOK t := by
  unfold step at h
  split at h
  · cases h
  · cases h
  · unfold dispatch at h
    split_ifs at h
    · cases h; intro _; rfl
    · cases h; trivial
    · cases h; exact Or.inr rfl
    · cases h; exact Or.inl rfl
    · split at h
      · split_ifs at h
        · cases h; exact Or.inl rfl
        · cases h; exact Or.inl rfl
      · cases h; exact Or.inl rfl
    · split at h
      · cases h; rfl
      · cases h
    · exact hash_ok h
    · split at h
      · exact classify_ok (ofToken_eq h)
      · cases h

end Silmaril.Proofs.Formats.SExp.CommonLisp
