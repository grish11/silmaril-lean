module

public import Silmaril.Formats.SExp.Racket.Defs
public import Silmaril.Formats.SExp.SchemeFamily.Thms
import Silmaril.Proofs.Formats.SExp.Racket.Basic

/-!
# Racket data: laws

* **roundtrip**: every well-formed datum is read back from its printed text (`parse?_print`),
  also as a prefix (`parsePrefix?_print`);
* **closure**: every datum read is well formed (`wf_of_parse?`): no unwritable symbol or keyword,
  markers only in marker position;
* **grammar**: `parse?_iff`.
-/

@[expose] public section

namespace Silmaril.Formats.Racket

open SExpReader

theorem laws : dialect.Laws := Silmaril.Proofs.Formats.SExp.Racket.laws

theorem printLaws : PrintLaws syntaxNotation lexer text := SchemeFamily.printLaws laws

theorem parse?_print {e : Datum} (hwf : syntaxNotation.wf e = true) :
    parse? (print e) = some e := by
  simpa [parse?, print] using SchemeFamily.read_print laws hwf

theorem parsePrefix?_print {e : Datum} (hwf : syntaxNotation.wf e = true)
    {rest : String} (hrest : Follows text rest.toList) :
    parsePrefix? (print e ++ rest) = some (e, rest) := by
  have := readPrefix_print printLaws hwf hrest
  simp [parsePrefix?, print, String.toList_append, this]

theorem wf_of_parse? {s : String} {e : Datum} (h : parse? s = some e) :
    syntaxNotation.wf e = true :=
  SchemeFamily.wf_of_read laws h

theorem parse?_iff (s : String) (e : Datum) :
    parse? s = some e ↔
      ∃ ts r, lexer.Emits s.toList ts r ∧ (lexer.next r).isEof = true ∧ Gram .datum ts e :=
  read_iff lexer

end Silmaril.Formats.Racket
