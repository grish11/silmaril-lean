module

public import Silmaril.Formats.SExp.Lexical.Defs
import Silmaril.Proofs.Formats.SExp.Lexical.Basic

/-!
# Lexical building blocks: each scanner inverts its printer
-/

@[expose] public section

namespace Silmaril.Formats.SExpLexical

theorem takeToken_append {p : Char → Bool} {w rest : List Char}
    (hw : ∀ c ∈ w, p c = true) (hr : ∀ c r, rest = c :: r → p c = false) :
    takeToken p (w ++ rest) = (w, rest) :=
  Silmaril.Proofs.Formats.SExp.Lexical.takeToken_append hw hr

theorem readQuoted_escape {q : Char} {esc : Char → Option Char}
    (hb : esc '\\' = some '\\') (hq : esc q = some q) (hqb : q ≠ '\\') (w rest : List Char) :
    readQuoted q esc (escapeQuoted q w ++ q :: rest) = some (w, rest) :=
  Silmaril.Proofs.Formats.SExp.Lexical.readQuoted_escape hb hq hqb w rest

theorem digits?_natText (n : Nat) : digits? (natText n) = some n :=
  Silmaril.Proofs.Formats.SExp.Lexical.digits?_natText n

theorem int?_intText (n : Int) : int? (intText n) = some n :=
  Silmaril.Proofs.Formats.SExp.Lexical.int?_intText n

theorem rational?_ratText (q : ℚ) : rational? (ratText q) = some q :=
  Silmaril.Proofs.Formats.SExp.Lexical.rational?_ratText q

theorem readDecimal_text {isMarker : Char → Bool} {m : Char} (hm : isMarker m = true)
    (hmd : m.isDigit = false) (hmp : m ≠ '.') (d : Decimal) :
    readDecimal isMarker (Decimal.text m d) = some (d, some m) :=
  Silmaril.Proofs.Formats.SExp.Lexical.readDecimal_text hm hmd hmp d

end Silmaril.Formats.SExpLexical
