module

public import Silmaril.Formats.SExp.Clojure.Defs
public import Silmaril.Formats.SExp.Reader.Thms
import Silmaril.Proofs.Formats.SExp.Clojure.Basic
import Silmaril.Proofs.Formats.SExp.Clojure.Equal
import Silmaril.Proofs.Formats.SExp.Clojure.Fuel

/-!
# Clojure data syntax: laws

* the lexer respects the encoding: it emits only plain atoms, the collection markers as the heads
  of their own openers, and abbreviation prefixes with plain symbol heads (`step_tokenOK`); in
  particular it never emits the consing dot (`step_ne_dot`), so no Clojure text reads as an
  improper list (`wf_valid_of_parse?`, with `syntaxNotation.listDotted = false`);
* **roundtrip**: every well-formed, valid datum is read back exactly from its printed text
  (`parse?_print`), also as a prefix (`parsePrefix?_print`); printing is injective on them
  (`print_injective`), so vectors, maps, sets and lists, `nil` and `()`, symbols, keywords,
  strings, longs and BigInts, doubles and BigDecimals all stay distinct;
* **key equality**: `equal?` decides Clojure's key equality `Equal` (an inductive specification,
  recursive through lists, vectors, maps and sets) wherever it answers (`equal?_sound`); an accepted map or set literal
  has pairwise unequal keys (`map_literal_ok`, `set_literal_ok`, through `issue_cons_none`), and a
  reported duplicate is a genuine pair of equal keys (`keysIssue_duplicate`); the fuel always
  suffices (`equal?_isSome`), so no text is rejected as `unsupported`
  (`parseError?_ne_unsupported`);
* **grammar**: `parse?` accepts exactly the texts whose lexed token string derives a datum in the
  shared phrase grammar, followed only by atmosphere, whose collections are `valid` (`parse?_iff`).
-/

@[expose] public section

namespace Silmaril.Formats.Clojure

open SExpReader

theorem printLaws : PrintLaws syntaxNotation lexer text :=
  Silmaril.Proofs.Formats.SExp.Clojure.printLaws

theorem step_tokenOK {s s' : List Char} {t : Token Atom Closer} (h : step s = .token t s') :
    syntaxNotation.TokenOK t :=
  Silmaril.Proofs.Formats.SExp.Clojure.step_tokenOK h

/-- Clojure has no dotted pairs: the lexer never emits the dot. -/
theorem step_ne_dot {s s' : List Char} {t : Token Atom Closer} (h : step s = .token t s') :
    t ≠ .dot := by
  rintro rfl
  have := Silmaril.Proofs.Formats.SExp.Clojure.step_guard h
  simp [tokenOK] at this

/-- Reader results are well formed (so in particular proper: no list has a dotted tail) and
their maps and sets are valid. -/
theorem wf_valid_of_parse? {s : String} {e : Datum} (h : parse? s = some e) :
    syntaxNotation.wf e = true ∧ valid e = true := by
  simp only [parse?, Option.filter_eq_some_iff] at h
  exact ⟨wf_of_read syntaxNotation (L := lexer) (fun _ _ _ hs => step_tokenOK hs) h.1, h.2⟩

/-- **Roundtrip.** -/
theorem parse?_print {e : Datum} (hwf : syntaxNotation.wf e = true) (hv : valid e = true) :
    parse? (print e) = some e := by
  have := read_print printLaws hwf
  simp [parse?, print, this, hv]

/-- **Prefix roundtrip**: reading stops exactly after a printed datum. -/
theorem parsePrefix?_print {e : Datum} (hwf : syntaxNotation.wf e = true) (hv : valid e = true)
    {rest : String} (h : Follows text rest.toList) :
    parsePrefix? (print e ++ rest) = some (e, rest) := by
  have := readPrefix_print printLaws hwf h
  simp [parsePrefix?, print, String.toList_append, this, hv]

theorem print_injective {a b : Datum} (ha : syntaxNotation.wf a = true) (hva : valid a = true)
    (hb : syntaxNotation.wf b = true) (hvb : valid b = true) (h : print a = print b) : a = b := by
  have := congrArg parse? h
  rwa [parse?_print ha hva, parse?_print hb hvb, Option.some.injEq] at this

/-- **Grammar characterization** of `parse?`. -/
theorem parse?_iff (s : String) (e : Datum) :
    parse? s = some e ↔
      (∃ ts r, lexer.Emits s.toList ts r ∧ (lexer.next r).isEof = true ∧ Gram .datum ts e) ∧
        valid e = true := by
  simp only [parse?, Option.filter_eq_some_iff, read_iff lexer]

/-! ## Key equality -/

/-- **`equal?` is sound**: whenever it answers, it answers Clojure's key equality. -/
theorem equal?_sound {a b : Value} {r : Bool} (h : equal? a b = some r) :
    Equal a b ↔ r = true :=
  Silmaril.Proofs.Formats.SExp.Clojure.equal?_sound a b r h

theorem keysIssue_none {vs : List Value} (h : keysIssue vs = none) :
    vs.Pairwise (fun a b => ¬ Equal a b) :=
  Silmaril.Proofs.Formats.SExp.Clojure.keysIssue_none vs h

theorem keysIssue_duplicate {vs : List Value} (h : keysIssue vs = some .duplicate) :
    ¬ vs.Pairwise (fun a b => ¬ Equal a b) :=
  Silmaril.Proofs.Formats.SExp.Clojure.keysIssue_duplicate vs h

/-- An accepted map literal has an even number of forms and pairwise unequal keys. -/
theorem map_literal_ok {r : Datum} (h : literalIssue .map r = none) :
    (elems r).length % 2 = 0 ∧ ∃ vs, (keysOf (elems r)).mapM toValue = some vs ∧
      vs.Pairwise (fun a b => ¬ Equal a b) :=
  Silmaril.Proofs.Formats.SExp.Clojure.map_literal_ok h

/-- An accepted set literal has pairwise unequal elements. -/
theorem set_literal_ok {r : Datum} (h : literalIssue .set r = none) :
    ∃ vs, (elems r).mapM toValue = some vs ∧ vs.Pairwise (fun a b => ¬ Equal a b) :=
  Silmaril.Proofs.Formats.SExp.Clojure.set_literal_ok h

/-- Validity is checked at every node. -/
theorem issue_cons_none {x r : Datum} (h : issue (.cons x r) = none) :
    (∀ m, x = .atom m → literalIssue m r = none) ∧ issue x = none ∧ issue r = none :=
  Silmaril.Proofs.Formats.SExp.Clojure.issue_cons_none h

/-- **Fuel adequacy**: `equal?` answers whenever every map in both values has an even number of
forms. Every recursive call compares elements of the first value, so `size a + 1` steps suffice
and the fuel `size a + size b + 1` is enough. -/
theorem equal?_isSome {a b : Value} (ha : a.evenMaps = true) (hb : b.evenMaps = true) :
    (equal? a b).isSome = true :=
  Silmaril.Proofs.Formats.SExp.Clojure.equal?_isSome ha hb

/-- On well-formed data, the literal check never reports an undecided comparison. -/
theorem issue_ne_unsupported {e : Datum} (h : syntaxNotation.wf e = true) :
    issue e ≠ some .unsupported :=
  (Silmaril.Proofs.Formats.SExp.Clojure.issue_ne_unsupported e).1 h

/-- **No text is rejected as `unsupported`**: every key comparison the reader makes is decided;
texts fail only for syntax, odd maps or genuine duplicates. -/
theorem parseError?_ne_unsupported (s : String) :
    parseError? s ≠ some (.literal .unsupported) := by
  simp only [parseError?, parseE?]
  cases hr : read lexer s.toList with
  | none => simp
  | some e =>
      have hwf := SExpReader.wf_of_read syntaxNotation (fun _ _ _ h => step_tokenOK h) hr
      have hne := issue_ne_unsupported hwf
      cases hi : issue e with
      | none => simp [hi]
      | some i =>
          rw [hi] at hne
          simp only [hi]
          intro h
          simp only [Option.some.injEq, ParseError.literal.injEq] at h
          exact hne (by rw [h])

theorem parse?_eq_toOption (s : String) : parse? s = (parseE? s).toOption := by
  simp only [parse?, parseE?]
  cases read lexer s.toList with
  | none => rfl
  | some e => cases h : issue e <;> simp [Option.filter, valid, h, Except.toOption]

end Silmaril.Formats.Clojure
