module

public import Silmaril.Formats.SExp.Clojure.Defs
public import Silmaril.Formats.SExp.Reader.Thms
import Silmaril.Proofs.Formats.SExp.Clojure.Basic

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

end Silmaril.Formats.Clojure
