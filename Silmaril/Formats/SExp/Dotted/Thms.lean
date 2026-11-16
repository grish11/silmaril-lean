module

public import Silmaril.Formats.SExp.Dotted.Defs
public import Silmaril.Formats.SExp.Reader.Thms
public import Silmaril.Formats.Category.Thms
import Silmaril.Proofs.Formats.SExp.Dotted.Basic

/-!
# Dotted S-expression text: laws

* **roundtrip**: every datum, proper or improper, is read back exactly from its printed text
  (`parse?_print`), also as a prefix followed by a delimiter (`parsePrefix?_print`); hence
  printing is injective (`print_injective`), so no symbol/string distinction is lost;
* **grammar**: `parse?` accepts exactly the texts whose token string (as lexed) derives a datum in
  the shared phrase grammar, followed only by atmosphere (`parse?_iff`); a derivation is unique
  (`SExpReader.gram_unique`);
* the format over UTF-8 bytes is unambiguous (`format_unambiguous`).
-/

@[expose] public section

namespace Silmaril.Formats.DottedSExp

open SExpReader

theorem printLaws : PrintLaws syntaxNotation lexer text :=
  Silmaril.Proofs.Formats.SExp.Dotted.printLaws

/-- Every datum has a written form. -/
theorem wf (e : Datum) : syntaxNotation.wf e = true :=
  (Silmaril.Proofs.Formats.SExp.Dotted.wf_all e).1

/-- **Roundtrip** for all dotted S-expressions. -/
theorem parse?_print (e : Datum) : parse? (print e) = some e := by
  simpa [parse?, print] using read_print printLaws (wf e)

/-- **Prefix roundtrip**: reading stops exactly after a printed datum. -/
theorem parsePrefix?_print (e : Datum) {rest : String}
    (h : rest.toList = [] ∨ (∃ r, rest.toList = ' ' :: r) ∨ ∃ r, rest.toList = ')' :: r) :
    parsePrefix? (print e ++ rest) = some (e, rest) := by
  have hf : Follows text rest.toList := by
    rcases h with h | ⟨r, h⟩ | ⟨r, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨r, h⟩)
    · exact Or.inr (Or.inr ⟨(), r, h⟩)
  have := readPrefix_print printLaws (wf e) hf
  simp [parsePrefix?, print, String.toList_append, this]

theorem print_injective : Function.Injective print := by
  intro a b h
  have := congrArg parse? h
  rwa [parse?_print, parse?_print, Option.some.injEq] at this

/-- **Grammar characterization** of `parse?`. -/
theorem parse?_iff (s : String) (e : Datum) :
    parse? s = some e ↔
      ∃ ts r, lexer.Emits s.toList ts r ∧ (lexer.next r).isEof = true ∧ Gram .datum ts e :=
  read_iff lexer

theorem format_unambiguous : format.Unambiguous := Format.ofDecoder_unambiguous _

end Silmaril.Formats.DottedSExp
