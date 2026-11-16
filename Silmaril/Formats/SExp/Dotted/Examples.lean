module

public import Silmaril.Formats.SExp.Dotted.Thms

/-! # Dotted S-expression text: examples

Each example is checked by the kernel (`decide`) against the executable reader. -/

namespace Silmaril.Formats.DottedSExp

open SExp2

private def sym (s : String) : Datum := .atom (.symbol s)
private def str (s : String) : Datum := .atom (.string s)

/-! ## Accepted -/

example : parse? "(a . b)" = some (.cons (sym "a") (sym "b")) := by decide
example : parse? "(a b . c)" = some (.cons (sym "a") (.cons (sym "b") (sym "c"))) := by decide
example : parse? "(a . (b c))" = parse? "(a b c)" := by decide
example : parse? "(a . ())" = parse? "(a)" := by decide
example : parse? "()" = some .nil := by decide
example : parse? "((a . b) . (c . d))" =
    some (.cons (.cons (sym "a") (sym "b")) (.cons (sym "c") (sym "d"))) := by decide
example : parse? "  ; comment\n (a\t.\nb) ; trailing\n" = parse? "(a . b)" := by decide
example : parse? "(a.b .c ... a.)" =
    some (ofList [sym "a.b", sym ".c", sym "...", sym "a."]) := by decide
/-- Strings and symbols stay distinct. -/
example : parse? "(a \"a\")" = some (ofList [sym "a", str "a"]) := by decide
example : parse? "|a b|" = some (sym "a b") := by decide
example : parse? "\"x\\n\\\"y\\\\\"" = some (str "x\n\"y\\") := by decide
example : parse? "|.|" = some (sym ".") := by decide
/-- Delimiters end bare tokens: `a"b"` is two atoms. -/
example : parse? "(a\"b\")" = some (ofList [sym "a", str "b"]) := by decide
/-- An improper datum is not proper; a list is. -/
example : (parse? "(a . b)").all (fun e => decide (IsProper e)) = false := by decide
example : (parse? "(a (b . c))").all (fun e => decide (IsProper e)) = false := by decide
example : (parse? "(a (b c))").all (fun e => decide (IsProper e)) = true := by decide

/-! ## Rejected -/

example : parse? "." = none := by decide
example : parse? "( . a)" = none := by decide
example : parse? "(a . )" = none := by decide
example : parse? "(a . b c)" = none := by decide
example : parse? "(a . b . c)" = none := by decide
example : parse? "(a . . b)" = none := by decide
example : parse? "(a" = none := by decide
example : parse? "a)" = none := by decide
example : parse? ")" = none := by decide
example : parse? "" = none := by decide
example : parse? "\"abc" = none := by decide
example : parse? "\"\\q\"" = none := by decide
/-- `parse?` needs the whole input; `parsePrefix?` reads one datum and returns the rest. -/
example : parse? "(a) (b)" = none := by decide
example : parsePrefix? "(a) (b)" = some (ofList [sym "a"], " (b)") := by decide
example : parseAll? "(a . b) c \"d\" ; end" =
    some [.cons (sym "a") (sym "b"), sym "c", str "d"] := by decide

/-! ## Printing -/

example : print (.cons (sym "a b") (.cons (str "q\"") (sym "."))) =
    "(|a b| \"q\\\"\" . |.|)" := by decide
example : print (.cons (sym "a") (.cons (.cons (sym "b") (sym "c")) .nil)) = "(a (b . c))" := by
  decide

/-! ## UTF-8 bytes -/

/-- Non-ASCII symbols and strings decode from their UTF-8 bytes. -/
example : decode ⟨"(λ . \"é\")".toUTF8⟩ = some (.cons (sym "λ") (str "é")) := by decide
/-- Ill-formed UTF-8 is rejected: a stray byte, an overlong NUL, a surrogate, a truncated
sequence. -/
example : decode ⟨ByteArray.mk #[0xff]⟩ = none := by decide
example : decode ⟨ByteArray.mk #[0xc0, 0x80]⟩ = none := by decide
example : decode ⟨ByteArray.mk #[0x22, 0xed, 0xa0, 0x80, 0x22]⟩ = none := by decide
example : decode ⟨ByteArray.mk #[0x28, 0xe2, 0x82, 0x29]⟩ = none := by decide
/-- Newline, return and tab are written escaped, other control characters as themselves; both
read back (the byte roundtrip `decode_encode` covers every datum). -/
example : print (ofList [sym "λ", str "é\n\x01\t"]) = "(λ \"é\\n\x01\\t\")" := by decide
example : parse? "\"a\x01b\"" = some (str "a\x01b") := by decide
example : decode (encode (ofList [sym "a\nb", str "\x00\r"])) = some (ofList [sym "a\nb", str "\x00\r"]) :=
  decode_encode _

/-! ## The older parser `SExpParser.parseSExp2?`

On the texts the older printer writes, the two parsers agree (`agrees_on_printSExp2?`). Elsewhere
they differ, and the differences are deliberate: -/

/-- The older parser reads a lone `.` as a symbol; the dotted syntax rejects it. -/
example : SExpParser.parseSExp2? "." = some (.atom ".") := by decide +kernel
example : parse? "." = none := by decide
/-- `"` does not end a bare token in the older parser. -/
example : SExpParser.parseSExp2? "a\"b\"" = some (.atom "a\"b\"") := by decide +kernel
example : parse? "a\"b\"" = none := by decide
/-- The older parser decodes any `\c` as `c`; the dotted syntax rejects unknown escapes. -/
example : SExpParser.parseSExp2? "\"\\q\"" = some (.atom "q") := by decide +kernel
example : parse? "\"\\q\"" = none := by decide
/-- `|…|` quotes a symbol only in the dotted syntax. -/
example : SExpParser.parseSExp2? "(|a b|)" = some (ofList [.atom "|a", .atom "b|"]) := by
  decide +kernel
example : parse? "(|a b|)" = some (ofList [sym "a b"]) := by decide
/-- Form feed is whitespace only in the dotted syntax. -/
example : SExpParser.parseSExp2? "(a\x0cb)" = some (ofList [.atom "a\x0cb"]) := by decide +kernel
example : parse? "(a\x0cb)" = some (ofList [sym "a", sym "b"]) := by decide

end Silmaril.Formats.DottedSExp
