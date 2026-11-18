module

public import Silmaril.Formats.SExp.SchemeFamily.Defs
public import Silmaril.Formats.SExp.Reader.Thms
import Silmaril.Proofs.Formats.SExp.SchemeFamily.Print

/-!
# The Scheme-family reader: laws

For every dialect whose character classes satisfy `Dialect.Laws`:

* the lexer only produces tokens that respect the marker encoding (`step_tokenOK`), so every
  datum read is well formed (`wf_of_read`);
* every printed token is lexed back (`printLaws`), so every well-formed datum is read back from
  its printed text (`read_print`).
-/

@[expose] public section

namespace Silmaril.Formats.SchemeFamily

open SExpReader

variable {C : Type} {D : Dialect C}

theorem printLaws (hL : D.Laws) : PrintLaws D.syntaxNotation D.lexer D.text :=
  Silmaril.Proofs.Formats.SExp.SchemeFamily.printLaws hL

theorem step_tokenOK (hL : D.Laws) (s : List Char) (t : Token Atom C) (s' : List Char)
    (h : D.step s = .token t s') : D.syntaxNotation.TokenOK t :=
  Silmaril.Proofs.Formats.SExp.SchemeFamily.step_ok hL s t s' h

theorem read_print [DecidableEq C] (hL : D.Laws) {e : SExp2 Atom} (he : D.syntaxNotation.wf e = true) :
    read D.lexer (print D.syntaxNotation D.text e) = some e :=
  SExpReader.read_print (printLaws hL) he

theorem wf_of_read [DecidableEq C] (hL : D.Laws) {s : List Char} {e : SExp2 Atom} (h : read D.lexer s = some e) :
    D.syntaxNotation.wf e = true :=
  SExpReader.wf_of_read D.syntaxNotation (step_tokenOK hL) h

end Silmaril.Formats.SchemeFamily
