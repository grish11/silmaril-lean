module

public import Silmaril.Formats.SExp.CommonLisp.Defs
public import Silmaril.Formats.SExp.Reader.Thms
import Silmaril.Proofs.Formats.SExp.CommonLisp.Basic

/-!
# Common Lisp data syntax: laws

* the lexer lexes every printed token back (`printLaws`) and never produces a marker atom as an
  ordinary atom (`lexer_ok`);
* **roundtrip**: every well-formed datum (`syntaxNotation.wf`: vectors, backquote and comma
  markers in head position only, the dot only in lists) is read back exactly from its printed
  text (`parse?_print`), also as a prefix (`parsePrefix?_print`), so printing is injective on
  well-formed data and loses no atom distinction (symbol/keyword/qualified/uninterned names,
  rationals, float formats, strings, characters);
* **reader output is well formed** (`wf_of_parse?`), and `parse?` is characterized by the shared
  phrase grammar (`parse?_iff`).
-/

@[expose] public section

namespace Silmaril.Formats.CommonLisp

open SExpReader

theorem printLaws : PrintLaws syntaxNotation lexer text :=
  Silmaril.Proofs.Formats.SExp.CommonLisp.printLaws

theorem lexer_ok : ∀ s t s', lexer.step s = .token t s' → syntaxNotation.TokenOK t :=
  fun _ _ _ h => Silmaril.Proofs.Formats.SExp.CommonLisp.step_ok h

/-- **Roundtrip** for every well-formed Common Lisp datum, proper or dotted. -/
theorem parse?_print {e : Datum} (he : syntaxNotation.wf e = true) : parse? (print e) = some e := by
  simpa [parse?, print] using read_print printLaws he

/-- **Prefix roundtrip**: reading stops exactly after a printed datum. -/
theorem parsePrefix?_print {e : Datum} (he : syntaxNotation.wf e = true) {rest : String}
    (h : rest.toList = [] ∨ (∃ r, rest.toList = ' ' :: r) ∨ ∃ r, rest.toList = ')' :: r) :
    parsePrefix? (print e ++ rest) = some (e, rest) := by
  have hf : Follows text rest.toList := by
    rcases h with h | ⟨r, h⟩ | ⟨r, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨r, h⟩)
    · exact Or.inr (Or.inr ⟨(), r, h⟩)
  have := readPrefix_print printLaws he hf
  simp [parsePrefix?, print, String.toList_append, this]

theorem print_injective {a b : Datum} (ha : syntaxNotation.wf a = true)
    (hb : syntaxNotation.wf b = true) (h : print a = print b) : a = b := by
  have := congrArg parse? h
  rwa [parse?_print ha, parse?_print hb, Option.some.injEq] at this

/-- Everything read is well formed: markers occur only where their syntax puts them. -/
theorem wf_of_parse? {s : String} {e : Datum} (h : parse? s = some e) :
    syntaxNotation.wf e = true :=
  SExpReader.wf_of_read syntaxNotation lexer_ok h

/-- **Grammar characterization** of `parse?`. -/
theorem parse?_iff (s : String) (e : Datum) :
    parse? s = some e ↔
      ∃ ts r, lexer.Emits s.toList ts r ∧ (lexer.next r).isEof = true ∧ Gram .datum ts e :=
  read_iff lexer

end Silmaril.Formats.CommonLisp
