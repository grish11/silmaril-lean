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

end Silmaril.Formats.DottedSExp
