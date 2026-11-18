module

public import Silmaril.Formats.SExp.CommonLisp.Thms

/-! # Common Lisp data syntax: examples

Each example is checked by the kernel (`decide`) against the executable reader. -/

namespace Silmaril.Formats.CommonLisp

open SExp2

private def sym (s : String) : Datum := .atom (.symbol s)

/-! ## Accepted -/

/-- Unescaped characters are upcased; escaped ones are not. -/
example : parse? "(foo |Bar| f\\oo ab|c d|e)" =
    some (ofList [sym "FOO", sym "Bar", sym "FoO", sym "ABc dE"]) := by decide
example : parse? "(a . b)" = some (.cons (sym "A") (sym "B")) := by decide
example : parse? "(a b . c)" = some (.cons (sym "A") (.cons (sym "B") (sym "C"))) := by decide
example : parse? "(a . (b))" = parse? "(a b)" := by decide
example : parse? "(:kw p:s p::s #:g)" = some (ofList [.atom (.keyword "KW"),
    .atom (.qualified "P" "S" false), .atom (.qualified "P" "S" true),
    .atom (.uninterned "G")]) := by decide
attribute [local cbv_eval] Nat.ofDigitChars_eq_foldl in
example : parse? "(12 -7 5. +3 -3/6)" =
    some (ofList [.atom (.rational 12), .atom (.rational (-7)), .atom (.rational 5),
      .atom (.rational 3), .atom (.rational (-1/2))]) := by cbv
attribute [local cbv_eval] Nat.ofDigitChars_eq_foldl in
example : parse? "1.5" = some (.atom (.float ⟨false, 15, -1⟩ .default)) := by cbv
attribute [local cbv_eval] Nat.ofDigitChars_eq_foldl in
example : parse? "-.5d2" = some (.atom (.float ⟨true, 5, 1⟩ .double)) := by cbv
attribute [local cbv_eval] Nat.ofDigitChars_eq_foldl in
example : parse? "1E3" = some (.atom (.float ⟨false, 1, 3⟩ .default)) := by cbv
example : parse? "\"a\\\"b\\q\"" = some (.atom (.string "a\"bq")) := by decide
example : parse? "(#\\a #\\( #\\Space #\\newline)" =
    some (ofList [.atom (.character 'a'), .atom (.character '('), .atom (.character ' '),
      .atom (.character '\n')]) := by decide
example : parse? "'x" = some (ofList [sym "QUOTE", sym "X"]) := by decide
example : parse? "#'f" = some (ofList [sym "FUNCTION", sym "F"]) := by decide
example : parse? "#(a b)" = some (.cons (.atom .vector) (ofList [sym "A", sym "B"])) := by decide
example : parse? "`(a ,b ,@c)" = some (ofList [.atom .backquote, ofList [sym "A",
    ofList [.atom .comma, sym "B"], ofList [.atom .commaAt, sym "C"]]]) := by decide
/-- A vector as a dotted tail stays a vector. -/
example : parse? "(a . #(b))" =
    some (.cons (sym "A") (.cons (.atom .vector) (ofList [sym "B"]))) := by decide
example : parse? "; c\n #| a #| nested |# b |# x" = some (sym "X") := by decide
/-- `1+` is not a potential number (it ends in a sign): a symbol. -/
example : parse? "1+" = some (sym "1+") := by decide
example : parse? "|1|" = some (sym "1") := by decide

/-! ## Rejected -/

example : parse? "(a . b c)" = none := by decide
example : parse? "( . a)" = none := by decide
example : parse? "(a . )" = none := by decide
example : parse? "(a . b . c)" = none := by decide
example : parse? "." = none := by decide
example : parse? "..." = none := by decide
example : parse? "#(a . b)" = none := by decide
example : parse? "#.(launch)" = none := by decide
example : parse? "#+sbcl x" = none := by decide
example : parse? "#1=(a . #1#)" = none := by decide
example : parse? "#x1F" = none := by decide
example : parse? "a:b:c" = none := by decide
example : parse? "::a" = none := by decide
example : parse? "1e" = none := by decide
example : parse? "#\\Bogus" = none := by decide
example : parse? "#| unterminated" = none := by decide
example : parse? "(a) b" = none := by decide
example : parsePrefix? "(a) b" = some (ofList [sym "A"], " b") := by decide

/-! ## Printing -/

example : print (ofList [sym "FOO", sym "foo", .atom (.keyword "K"), sym "1"]) =
    "(FOO |foo| :K |1|)" := by decide
example : print (ofList [.atom .backquote, ofList [sym "A", ofList [.atom .comma, sym "B"]]]) =
    "` (A , B)" := by decide

end Silmaril.Formats.CommonLisp
