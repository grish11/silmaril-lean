module

public import Silmaril.Formats.SExp.Clojure.Defs
import Silmaril.Proofs.Formats.SExp.Lexical.Basic

/-! # Proofs: the Clojure lexer reads back its printed tokens -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Clojure

open Silmaril.Formats Silmaril.Formats.SExpReader Silmaril.Formats.SExpLexical
open Silmaril.Formats.Clojure
open Silmaril.Proofs.Formats.SExp.Lexical

/-! ## Characters -/

theorem delim_cases {d : Char} (h : isDelimiter d = true) :
    d ∈ [' ', '\t', '\n', '\r', ',', '\x0c', '"', ';', '@', '^', '`', '~', '(', ')', '[', ']',
      '{', '}', '\\'] := by
  simp only [isDelimiter, isSpace, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem nonDelim_of {p : Char → Bool}
    (hp : ∀ d ∈ [' ', '\t', '\n', '\r', ',', '\x0c', '"', ';', '@', '^', '`', '~', '(', ')', '[',
      ']', '{', '}', '\\'], p d = false) {d : Char} (h : p d = true) : isDelimiter d = false := by
  cases hd : isDelimiter d
  · rfl
  · have := hp d (delim_cases hd); rw [this] at h; cases h

theorem nameChar_nonDelim {d : Char} (h : nameChar d = true) : isDelimiter d = false :=
  nonDelim_of (p := nameChar) (by decide) h

theorem digit_nonDelim {d : Char} (h : d.isDigit = true) : isDelimiter d = false :=
  nonDelim_of (p := Char.isDigit) (by decide) h

theorem nameChar_ne {d : Char} (h : nameChar d = true) : d ≠ ':' ∧ d ≠ '/' := by
  constructor <;> rintro rfl <;> simp [nameChar] at h

/-! ## Atmosphere and dispatch -/

theorem skip_space (s : List Char) : skip false (' ' :: s) = skip false s := by
  simp [skip, isSpace]

theorem skip_head {c : Char} (r : List Char) (hs : isSpace c = false) (hc : c ≠ ';') :
    skip false (c :: r) = c :: r := by
  simp [skip, hs, hc]

theorem step_space (s : List Char) : step (' ' :: s) = step s := by
  unfold step rawStep; rw [skip_space]

theorem rawStep_bare {c : Char} (r : List Char) (h1 : isDelimiter c = false) (h2 : c ≠ '\'')
    (h3 : c ≠ '#') : rawStep (c :: r) = bareToken (c :: r) := by
  simp only [isDelimiter, isSpace, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsp, hsp2⟩, hsp3⟩, hsp4⟩, hcomma⟩, hff⟩, hq⟩, hsemi⟩, hat⟩, hcaret⟩,
    hbt⟩, htilde⟩, hlp⟩, hrp⟩, hlb⟩, hrb⟩, hlc⟩, hrc⟩, hbs⟩ := h1
  have hs : isSpace c = false := by simp [isSpace, hsp, hsp2, hsp3, hsp4, hcomma, hff]
  unfold rawStep
  rw [skip_head _ hs hsemi]
  simp [hq, hat, hbt, htilde, hlp, hrp, hlb, hrb, hlc, hrc, hbs, h2, h3, hcaret]

/-- What may follow a printed atom starts with a delimiter. -/
theorem delim_of_follows {rest : List Char} (h : Follows text rest) :
    ∀ c r, rest = c :: r → (!isDelimiter c) = false := by
  rintro c r rfl
  rcases h with h | ⟨r', h⟩ | ⟨cl, r', h⟩
  · cases h
  · cases h; decide
  · cases cl <;> simp only [text, List.cons_append, List.nil_append, List.cons.injEq] at h <;>
      (obtain ⟨rfl, rfl⟩ := h; decide)

theorem step_of_raw {s rest : List Char} {t : Token Atom Closer}
    (h : rawStep s = .token t rest) (hok : tokenOK t = true) : step s = .token t rest := by
  simp [step, h, hok]

/-- A bare token of non-delimiters, read by `classify`. -/
theorem step_bare {c : Char} {r0 w rest : List Char} {a : Atom} (hw : w = c :: r0)
    (h1 : isDelimiter c = false) (h2 : c ≠ '\'') (h3 : c ≠ '#')
    (hall : ∀ d ∈ w, isDelimiter d = false) (hrest : Follows text rest)
    (hcl : classify w = some a) (hrole : role a = .plain) :
    step (w ++ rest) = .token (.atom a) rest := by
  have htake := takeToken_append (p := fun c => !isDelimiter c) (w := w)
    (fun d hd => by simp [hall d hd]) (delim_of_follows hrest)
  refine step_of_raw ?_ (by simp [tokenOK, hrole, Role.isPlain])
  subst hw
  rw [List.cons_append, rawStep_bare _ h1 h2 h3, ← List.cons_append]
  unfold bareToken
  rw [htake]
  simp [hcl]

/-! ## Numbers -/

theorem natText_getLast (n : Nat) : ∃ c, (natText n).getLast? = some c ∧ c.isDigit = true := by
  cases h : (natText n).getLast? with
  | none => simp [List.getLast?_eq_none_iff, natText_ne_nil] at h
  | some c => exact ⟨c, rfl, natText_isDigit n c (List.mem_of_getLast? h)⟩

theorem intText_getLast (n : Int) : ∃ c, (intText n).getLast? = some c ∧ c.isDigit = true := by
  unfold intText
  split
  · rw [show '-' :: natText n.natAbs = ['-'] ++ natText n.natAbs from rfl,
      List.getLast?_append_of_ne_nil _ (natText_ne_nil _)]
    exact natText_getLast _
  · exact natText_getLast _

theorem intText_head (n : Int) :
    ∃ c r, intText n = c :: r ∧ (c.isDigit = true ∨ (c = '-' ∧ ∃ d r', r = d :: r' ∧ d.isDigit = true)) := by
  unfold intText
  split
  · obtain ⟨d, r', h, hd⟩ := natText_head n.natAbs
    exact ⟨'-', _, rfl, Or.inr ⟨rfl, d, r', h, hd⟩⟩
  · obtain ⟨d, r', h, hd⟩ := natText_head n.toNat
    exact ⟨d, r', h, Or.inl hd⟩

theorem numericStart_intText (n : Int) (t : List Char) : numericStart (intText n ++ t) = true := by
  obtain ⟨c, r, h, hc⟩ := intText_head n
  rw [h]
  rcases hc with hc | ⟨rfl, d, r', rfl, hd⟩
  · simp [numericStart, hc]
  · simp [numericStart, isSign, hd]

theorem intText_nonDelim (n : Int) : ∀ d ∈ intText n, isDelimiter d = false := by
  intro d hd
  rcases intText_chars n d hd with h | rfl
  · exact digit_nonDelim h
  · decide

theorem intToken?_intText (n : Int) : intToken? (intText n) = some n := by
  simp [intToken?, int?_intText]

theorem getLast_ne_of_digit {l : List Char} {c : Char} (h : l.getLast? = some c)
    (hc : c.isDigit = true) : l.getLast? ≠ some 'N' ∧ l.getLast? ≠ some 'M' := by
  rw [h]
  constructor <;> rintro ⟨⟩ <;> simp at hc

theorem classify_int (n : Int) (h : longRange n = true) :
    classify (intText n) = some (.integer n false) := by
  obtain ⟨c, hl, hc⟩ := intText_getLast n
  obtain ⟨hN, hM⟩ := getLast_ne_of_digit hl hc
  have hs := numericStart_intText n []
  rw [List.append_nil] at hs
  simp [classify, hs, classifyNumber, hN, hM, intToken?_intText, h]

theorem classify_bigint (n : Int) : classify (intText n ++ ['N']) = some (.integer n true) := by
  simp [classify, numericStart_intText, classifyNumber, intToken?_intText]

theorem decimal_text_eq (d : Decimal) :
    Decimal.text 'e' d =
      (if d.negative then ['-'] else []) ++ (natText d.significand ++ 'e' :: intText d.exponent) := by
  simp [Decimal.text]

theorem decimal_getLast (d : Decimal) :
    ∃ c, (Decimal.text 'e' d).getLast? = some c ∧ c.isDigit = true := by
  rw [decimal_text_eq, List.getLast?_append_of_ne_nil _ (by simp),
    List.getLast?_append_of_ne_nil _ (by simp),
    show 'e' :: intText d.exponent = ['e'] ++ intText d.exponent from rfl,
    List.getLast?_append_of_ne_nil _ (intText_ne_nil _)]
  exact intText_getLast _

theorem numericStart_decimal (d : Decimal) (t : List Char) :
    numericStart (Decimal.text 'e' d ++ t) = true := by
  obtain ⟨c, r, h, hc⟩ := natText_head d.significand
  rw [decimal_text_eq, h]
  cases d.negative <;> simp [numericStart, isSign, hc]

theorem digits?_of_not_digit {cs : List Char} (h : ∃ c ∈ cs, c.isDigit = false) :
    digits? cs = none := by
  obtain ⟨c, hc, hd⟩ := h
  unfold digits?
  rw [ite_eq_right]
  rintro ⟨-, hall⟩
  rw [List.all_eq_true] at hall
  rw [hall c hc] at hd; cases hd

theorem int?_decimal (d : Decimal) : int? (Decimal.text 'e' d) = none := by
  obtain ⟨c, r, h, hc⟩ := natText_head d.significand
  have hs := not_sign_of_isDigit hc
  have he : ∀ l : List Char, ∃ x ∈ l ++ 'e' :: intText d.exponent, x.isDigit = false :=
    fun l => ⟨'e', by simp, by decide⟩
  rw [decimal_text_eq]
  cases d.negative
  · simp only [Bool.false_eq_true, ite_false, List.nil_append]
    rw [h]
    simp only [List.cons_append, int?, hs.1, hs.2, ite_false]
    rw [← List.cons_append, ← h, digits?_of_not_digit (he _)]
    rfl
  · simp only [ite_true, List.cons_append, List.nil_append, int?, ite_true]
    rw [digits?_of_not_digit (he _)]
    rfl

theorem decimal_nonDelim (d : Decimal) : ∀ x ∈ Decimal.text 'e' d, isDelimiter x = false := by
  intro x hx
  rw [decimal_text_eq] at hx
  simp only [List.mem_append, List.mem_cons] at hx
  rcases hx with hx | hx | rfl | hx
  · have : x = '-' := by split at hx <;> simp_all
    subst this; decide
  · exact digit_nonDelim (natText_isDigit _ x hx)
  · decide
  · exact intText_nonDelim _ x hx

theorem readDecimal_e (d : Decimal) : readDecimal isExp (Decimal.text 'e' d) = some (d, some 'e') :=
  readDecimal_text (by decide) (by decide) (by decide) d

theorem classify_float (d : Decimal) : classify (Decimal.text 'e' d) = some (.float d false) := by
  obtain ⟨c, hl, hc⟩ := decimal_getLast d
  obtain ⟨hN, hM⟩ := getLast_ne_of_digit hl hc
  have hs := numericStart_decimal d []
  rw [List.append_nil] at hs
  simp [classify, hs, classifyNumber, hN, hM, intToken?, int?_decimal, readDecimal_e]

theorem classify_bigdec (d : Decimal) :
    classify (Decimal.text 'e' d ++ ['M']) = some (.float d true) := by
  simp [classify, numericStart_decimal, classifyNumber, readDecimal_e]

/-! ## Symbols and keywords -/

theorem seg_facts {w : List Char} (h : validSegment w = true) :
    ∃ c r, w = c :: r ∧ nameChar c = true ∧ c ≠ '#' ∧ c ≠ '\'' ∧ numericStart w = false ∧
      (∀ d ∈ w, isDelimiter d = false ∧ d ≠ '/') := by
  cases w with
  | nil => simp [validSegment] at h
  | cons c r =>
      simp only [validSegment, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨hc, h1⟩, h2⟩, h3⟩, hall⟩, -⟩, -⟩ := h
      refine ⟨c, r, rfl, hc, h1, h2, h3, ?_⟩
      intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact ⟨nameChar_nonDelim hc, (nameChar_ne hc).2⟩
      · rcases hall d hd with h | rfl
        · exact ⟨nameChar_nonDelim h, (nameChar_ne h).2⟩
        · decide

theorem symParts_none {w : List Char} (hw : ∀ d ∈ w, d ≠ '/') :
    symParts w = some (none, String.ofList w) := by
  have := takeToken_append (p := fun c => c != '/') (w := w) (rest := [])
    (fun d hd => by simpa using hw d hd) (by simp)
  rw [List.append_nil] at this
  simp [symParts, this]

theorem symParts_some {a b : List Char} (ha : a ≠ []) (hall : ∀ d ∈ a, d ≠ '/') :
    symParts (a ++ '/' :: b) = some (some (String.ofList a), String.ofList b) := by
  have := takeToken_append (p := fun c => c != '/') (w := a) (rest := '/' :: b)
    (fun d hd => by simpa using hall d hd) (by intro c r h; cases h; rfl)
  simp [symParts, this, ha]

theorem numericStart_append {c : Char} {r t : List Char} (h : numericStart (c :: r) = false)
    (ht : ∀ d t', t = d :: t' → d.isDigit = false) : numericStart (c :: r ++ t) = false := by
  cases r with
  | nil =>
      cases t with
      | nil => simpa using h
      | cons d t' =>
          have hd : c.isDigit = false := by simpa [numericStart] using h
          simp [numericStart, hd, ht d t' rfl]
  | cons d r' => simpa [numericStart] using h

/-- Facts about the text of a symbol or keyword name with valid segments. -/
theorem symText_facts {ns : Option String} {n : String}
    (hns : ∀ s, ns = some s → validSegment s.toList = true)
    (hn : n.toList = ['/'] ∨ validSegment n.toList = true) :
    ∃ c r, symText ns n = c :: r ∧ isDelimiter c = false ∧ c ≠ '\'' ∧ c ≠ '#' ∧ c ≠ ':' ∧
      numericStart (c :: r) = false ∧ (∀ d ∈ symText ns n, isDelimiter d = false) ∧
      symParts (symText ns n) = some (ns, n) := by
  have hnchars : ∀ d ∈ n.toList, isDelimiter d = false := by
    rcases hn with hn | hn
    · rw [hn]; intro d hd; simp at hd; subst hd; decide
    · obtain ⟨_, _, _, _, _, _, _, hall⟩ := seg_facts hn
      exact fun d hd => (hall d hd).1
  cases ns with
  | none =>
      rcases hn with hn | hn
      · have : n = "/" := String.toList_inj.1 (by rw [hn]; rfl)
        subst this
        exact ⟨'/', [], rfl, by decide, by decide, by decide, by decide, by decide,
          by intro d hd; simp [symText] at hd; subst hd; decide, by decide⟩
      · obtain ⟨c, r, hcr, hc, h1, h2, hnum, hall⟩ := seg_facts hn
        refine ⟨c, r, hcr, nameChar_nonDelim hc, h2, h1, (nameChar_ne hc).1, hcr ▸ hnum,
          fun d hd => (hall d hd).1, ?_⟩
        simp only [symText]
        rw [symParts_none (fun d hd => (hall d hd).2), String.ofList_toList]
  | some ns =>
      obtain ⟨c, r, hcr, hc, h1, h2, hnum, hall⟩ := seg_facts (hns ns rfl)
      refine ⟨c, r ++ '/' :: n.toList, by simp [symText, hcr], nameChar_nonDelim hc, h2, h1,
        (nameChar_ne hc).1, ?_, ?_, ?_⟩
      · rw [← List.cons_append]
        exact numericStart_append (hcr ▸ hnum) (by intro d t' h; cases h; decide)
      · intro d hd
        simp only [symText, List.mem_append, List.mem_cons] at hd
        rcases hd with hd | rfl | hd
        · exact (hall d hd).1
        · decide
        · exact hnchars d hd
      · simp only [symText]
        rw [symParts_some (by simp [hcr]) (fun d hd => (hall d hd).2), String.ofList_toList,
          String.ofList_toList]

theorem classify_symbol {ns : Option String} {n : String} (h : symbolOK ns n = true) :
    classify (symText ns n) = some (.symbol ns n) := by
  have hns : ∀ s, ns = some s → validSegment s.toList = true := by
    rintro s rfl; simp only [symbolOK, Bool.and_eq_true] at h; exact h.1
  have hn : n.toList = ['/'] ∨ validSegment n.toList = true := by
    cases ns <;> simp only [symbolOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    · exact h.1.1.1
    · exact h.2
  obtain ⟨c, r, hcr, -, -, -, hcol, hnum, -, hparts⟩ := symText_facts hns hn
  rw [hcr] at hparts ⊢
  cases ns with
  | none =>
      simp only [symbolOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      obtain ⟨⟨⟨-, h1⟩, h2⟩, h3⟩ := h
      simp [classify, hnum, hcol, hparts, h1, h2, h3, symbolOK, hn]
  | some ns =>
      simp only [symbolOK, Bool.and_eq_true] at h
      simp [classify, hnum, hcol, hparts, symbolOK, h.1, h.2]

theorem classify_keyword {ns : Option String} {n : String} (h : keywordOK ns n = true) :
    classify (':' :: symText ns n) = some (.keyword ns n) := by
  have hns : ∀ s, ns = some s → validSegment s.toList = true := by
    rintro s rfl; simp only [keywordOK, Bool.and_eq_true] at h; exact h.1
  have hn : n.toList = ['/'] ∨ validSegment n.toList = true := by
    cases ns <;> simp only [keywordOK, Bool.and_eq_true] at h
    · exact Or.inr h
    · exact Or.inr h.2
  obtain ⟨c, r, hcr, -, -, -, hcol, -, -, hparts⟩ := symText_facts hns hn
  have hnum : numericStart (':' :: symText ns n) = false := by
    rw [hcr]; simp [numericStart, isSign]
  unfold classify
  rw [hnum]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [hcr] at hparts ⊢
  simp [hcol, hparts, h]

/-! ## The lexing laws of atoms -/

theorem step_bare' {w rest : List Char} {a : Atom}
    (hhead : ∃ c r, w = c :: r ∧ isDelimiter c = false ∧ c ≠ '\'' ∧ c ≠ '#')
    (hall : ∀ d ∈ w, isDelimiter d = false) (hrest : Follows text rest)
    (hcl : classify w = some a) (hrole : role a = .plain) :
    step (w ++ rest) = .token (.atom a) rest := by
  obtain ⟨c, r, hw, h1, h2, h3⟩ := hhead
  exact step_bare hw h1 h2 h3 hall hrest hcl hrole

theorem intText_head' (n : Int) (t : List Char) :
    ∃ c r, intText n ++ t = c :: r ∧ isDelimiter c = false ∧ c ≠ '\'' ∧ c ≠ '#' := by
  obtain ⟨c, r, h, hc⟩ := intText_head n
  refine ⟨c, r ++ t, by simp [h], ?_⟩
  rcases hc with hc | ⟨rfl, -⟩
  · exact ⟨digit_nonDelim hc, by rintro rfl; simp at hc, by rintro rfl; simp at hc⟩
  · decide

theorem decimal_head' (d : Decimal) (t : List Char) :
    ∃ c r, Decimal.text 'e' d ++ t = c :: r ∧ isDelimiter c = false ∧ c ≠ '\'' ∧ c ≠ '#' := by
  obtain ⟨c, r, h, hc⟩ := natText_head d.significand
  rw [decimal_text_eq, h]
  cases d.negative
  · exact ⟨c, r ++ 'e' :: (intText d.exponent ++ t), by simp, digit_nonDelim hc,
      by rintro rfl; simp at hc, by rintro rfl; simp at hc⟩
  · exact ⟨'-', c :: (r ++ 'e' :: (intText d.exponent ++ t)), by simp, by decide, by decide,
      by decide⟩

theorem step_string (s : String) (rest : List Char) :
    step (atomText (.string s) ++ rest) = .token (.atom (.string s)) rest := by
  have hr := readQuoted_escape (q := '"') (esc := escape) (by decide) (by decide) (by decide)
    s.toList rest
  refine step_of_raw ?_ (by simp [tokenOK, role, Role.isPlain])
  simp only [atomText, List.cons_append, List.append_assoc, List.cons_append, List.nil_append]
  unfold rawStep
  rw [skip_head _ (by decide) (by decide)]
  simp [hr]

theorem charName_spec {c : Char} {nm : List Char} (h : charName c = some nm) :
    ∃ c0 w0, nm = c0 :: w0 ∧ w0 ≠ [] ∧ (∀ d ∈ w0, isDelimiter d = false) ∧
      charOfName nm = some c := by
  unfold charName at h
  split_ifs at h <;> (cases h; subst_vars; exact ⟨_, _, rfl, by decide, by decide, by decide⟩)

theorem rawStep_backslash (r : List Char) : rawStep ('\\' :: r) = charToken r := by
  unfold rawStep
  rw [skip_head _ (by decide) (by decide)]
  simp

theorem step_char (c : Char) (rest : List Char) (hrest : Follows text rest) :
    step (atomText (.char c) ++ rest) = .token (.atom (.char c)) rest := by
  refine step_of_raw ?_ (by simp [tokenOK, role, Role.isPlain])
  simp only [atomText, List.cons_append]
  rw [rawStep_backslash]
  unfold charText
  split
  · rename_i nm hnm
    obtain ⟨c0, w0, rfl, hne, hall, hname⟩ := charName_spec hnm
    have htake := takeToken_append (p := fun c => !isDelimiter c) (w := w0)
      (fun d hd => by simp [hall d hd]) (delim_of_follows hrest)
    simp only [List.cons_append, charToken, htake, hne, ite_false, hname]
  · have htake := takeToken_append (p := fun c => !isDelimiter c) (w := []) (rest := rest)
      (by simp) (delim_of_follows hrest)
    simp only [List.nil_append] at htake
    simp [charToken, htake]

theorem step_atom (a : Atom) (rest : List Char) (hrole : role a = .plain)
    (hrest : Follows text rest) : step (text (.atom a) ++ rest) = .token (.atom a) rest := by
  have htext : text (.atom a) = atomText a := by simp [text, hrole, Role.isPlain]
  rw [htext]
  cases a with
  | nil =>
      exact step_bare' (w := ['n', 'i', 'l']) ⟨'n', _, rfl, by decide, by decide, by decide⟩
        (by decide) hrest (by decide) hrole
  | boolean b =>
      cases b
      · exact step_bare' (w := ['f', 'a', 'l', 's', 'e'])
          ⟨'f', _, rfl, by decide, by decide, by decide⟩ (by decide) hrest (by decide) hrole
      · exact step_bare' (w := ['t', 'r', 'u', 'e'])
          ⟨'t', _, rfl, by decide, by decide, by decide⟩ (by decide) hrest (by decide) hrole
  | integer n big =>
      cases big
      · have hl : longRange n = true := by simpa [role] using hrole
        have := step_bare' (intText_head' n []) (by simpa using intText_nonDelim n) hrest
          (by simpa using classify_int n hl) hrole
        simpa [atomText] using this
      · have hall : ∀ d ∈ intText n ++ ['N'], isDelimiter d = false := by
          intro d hd
          simp only [List.mem_append, List.mem_singleton] at hd
          rcases hd with hd | rfl
          · exact intText_nonDelim n d hd
          · decide
        have := step_bare' (intText_head' n ['N']) hall hrest (classify_bigint n) hrole
        simpa [atomText] using this
  | float d big =>
      cases big
      · have := step_bare' (decimal_head' d []) (by simpa using decimal_nonDelim d) hrest
          (by simpa using classify_float d) hrole
        simpa [atomText] using this
      · have hall : ∀ x ∈ Decimal.text 'e' d ++ ['M'], isDelimiter x = false := by
          intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact decimal_nonDelim d x hx
          · decide
        have := step_bare' (decimal_head' d ['M']) hall hrest (classify_bigdec d) hrole
        simpa [atomText] using this
  | string s => exact step_string s rest
  | char c => exact step_char c rest hrest
  | symbol ns n =>
      have hok : symbolOK ns n = true := by
        simp only [role] at hrole; split at hrole
        · assumption
        · cases hrole
      have hns : ∀ s, ns = some s → validSegment s.toList = true := by
        rintro s rfl; simp only [symbolOK, Bool.and_eq_true] at hok; exact hok.1
      have hn : n.toList = ['/'] ∨ validSegment n.toList = true := by
        cases ns <;> simp only [symbolOK, Bool.and_eq_true, Bool.or_eq_true,
          decide_eq_true_eq] at hok
        · exact hok.1.1.1
        · exact hok.2
      obtain ⟨c, r, hcr, h1, h2, h3, -, -, hall, -⟩ := symText_facts hns hn
      exact step_bare' ⟨c, r, hcr, h1, h2, h3⟩ hall hrest (classify_symbol hok) hrole
  | keyword ns n =>
      have hok : keywordOK ns n = true := by
        simp only [role] at hrole; split at hrole
        · assumption
        · cases hrole
      have hns : ∀ s, ns = some s → validSegment s.toList = true := by
        rintro s rfl; simp only [keywordOK, Bool.and_eq_true] at hok; exact hok.1
      have hn : n.toList = ['/'] ∨ validSegment n.toList = true := by
        cases ns <;> simp only [keywordOK, Bool.and_eq_true] at hok
        · exact Or.inr hok
        · exact Or.inr hok.2
      obtain ⟨c, r, hcr, -, -, -, -, -, hall, -⟩ := symText_facts hns hn
      refine step_bare' ⟨':', _, rfl, by decide, by decide, by decide⟩ ?_ hrest
        (classify_keyword hok) hrole
      intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · decide
      · exact hall d hd
  | vector => simp [role] at hrole
  | map => simp [role] at hrole
  | set => simp [role] at hrole

/-! ## The remaining laws -/

theorem not_dotted : ¬ syntaxNotation.Dotted := by
  rintro (h | ⟨m, c, h⟩)
  · cases h
  · cases m <;> simp [syntaxNotation, role] at h <;> split at h <;> cases h

theorem not_prefix (p : Atom) : syntaxNotation.role p ≠ .prefix := by
  cases p <;> simp [syntaxNotation, role] <;> split <;> simp

theorem tokenOK_sound {t : Token Atom Closer} (h : tokenOK t = true) :
    syntaxNotation.TokenOK t := by
  cases t with
  | atom a =>
      show role a = .plain
      simp only [tokenOK] at h
      cases hr : role a <;> simp_all [Role.isPlain]
  | «open» hd c d =>
      cases hd with
      | none =>
          simp only [tokenOK, Bool.not_eq_eq_eq_not, Bool.not_true] at h
          intro hd; rw [h] at hd; cases hd
      | some m => show role m = .coll c d; simpa [tokenOK] using h
  | close => trivial
  | dot => simp [tokenOK] at h
  | «prefix» p =>
      simp only [tokenOK] at h
      right; show role p = .plain
      cases hr : role p <;> simp_all [Role.isPlain]

theorem step_guard {s s' : List Char} {t : Token Atom Closer}
    (h : step s = .token t s') : tokenOK t = true := by
  unfold step at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · rename_i x hx; exact absurd h (hx t s')

theorem step_tokenOK {s s' : List Char} {t : Token Atom Closer}
    (h : step s = .token t s') : syntaxNotation.TokenOK t := by
  unfold step at h
  split at h
  · split at h
    · cases h; exact tokenOK_sound (by assumption)
    · cases h
  · rename_i x hx; exact absurd h (hx t s')

theorem lexer_step : lexer.step = Clojure.step := rfl

theorem printLaws : PrintLaws syntaxNotation lexer text where
  size_eq _ := rfl
  space := step_space
  eof := rfl
  atom a rest hrole hrest := step_atom a rest hrole hrest
  dot h := absurd h not_dotted
  openList rest := by
    show step (['('] ++ rest) = _
    unfold step rawStep
    rw [List.singleton_append, skip_head _ (by decide) (by decide)]
    simp [syntaxNotation, tokenOK]
  openColl m c d rest h := by
    have hm : (m = .vector ∨ m = .map ∨ m = .set) := by
      cases m <;> simp [syntaxNotation, role] at h ⊢ <;> split at h <;> cases h
    simp only [syntaxNotation] at h
    rcases hm with rfl | rfl | rfl <;> simp only [role, Role.coll.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> rw [lexer_step] <;> unfold Clojure.step rawStep <;>
      simp only [text, List.cons_append, List.nil_append] <;>
      rw [skip_head _ (by decide) (by decide)] <;> simp [tokenOK, role, hashToken]
  close c rest := by
    show step (text (.close c) ++ rest) = _
    unfold step rawStep
    cases c <;> simp only [text, List.cons_append, List.nil_append] <;>
      rw [skip_head _ (by decide) (by decide)] <;> simp [tokenOK]
  «prefix» p _ h := absurd h (not_prefix p)
  nonempty t := by
    cases t with
    | atom a =>
        simp only [text]
        split
        · rename_i hp
          cases a with
          | integer n big => simp [atomText, intText_ne_nil]
          | float d big => simp [atomText, Decimal.text]
          | symbol ns n =>
              have hok : symbolOK ns n = true := by
                simp only [role] at hp; split at hp
                · assumption
                · simp [Role.isPlain] at hp
              have hns : ∀ s, ns = some s → validSegment s.toList = true := by
                rintro s rfl; simp only [symbolOK, Bool.and_eq_true] at hok; exact hok.1
              have hn : n.toList = ['/'] ∨ validSegment n.toList = true := by
                cases ns <;> simp only [symbolOK, Bool.and_eq_true, Bool.or_eq_true,
                  decide_eq_true_eq] at hok
                · exact hok.1.1.1
                · exact hok.2
              obtain ⟨c, r, hcr, -⟩ := symText_facts hns hn
              simp [atomText, hcr]
          | boolean b => cases b <;> simp [atomText]
          | _ => simp [atomText]
        · simp
    | «open» hd c d =>
        rcases hd with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [text]
    | close c => cases c <;> simp [text]
    | _ => simp [text]

end Silmaril.Proofs.Formats.SExp.Clojure
