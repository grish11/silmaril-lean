module

public import Silmaril.Formats.SExp.Racket.Thms

/-! # Racket data: examples, checked by the kernel against the reader -/

namespace Silmaril.Formats.Racket

open SExp2 SchemeFamily

private def sym (s : String) : Datum := .atom (.symbol s)

/-! ## Accepted -/

/-- The three bracket shapes read as the same list. -/
example : parse? "[a {b} (c)]" = parse? "(a (b) (c))" := by decide
example : parse? "[a . b]" = some (.cons (sym "a") (sym "b")) := by decide
example : parse? "(#:key #:|k w| #&x)" = some (ofList
    [.atom (.keyword "key"), .atom (.keyword "k w"), .cons (.atom .box) (ofList [sym "x"])]) := by
  decide
example : parse? "#'(a #,b #,@c)" =
    parse? "(syntax (a (unsyntax b) (unsyntax-splicing c)))" := by decide
example : parse? "(a#b λ |x y|)" = some (ofList [sym "a#b", sym "λ", sym "x y"]) := by decide
example : parse? "(#t #true #\\nul #\\x \"\\e\")" = some (ofList
    [.atom (.boolean true), .atom (.boolean true), .atom (.char '\x00'), .atom (.char 'x'),
     .atom (.string "\x1b")]) := by decide
/-- `,` `'` and `` ` `` are delimiters in Racket. -/
example : parse? "(a'b)" = parse? "(a (quote b))" := by decide

/-! ## Rejected -/

example : parse? "#0=(a . #0#)" = none := by decide
example : parse? "(1 . < . 2)" = none := by decide
example : parse? "#;a b" = none := by decide
example : parse? "#hash((a . 1))" = none := by decide
example : parse? "#\"bytes\"" = none := by decide
example : parse? "a\\ b" = none := by decide
example : parse? "a|b|" = none := by decide
example : parse? "(a]" = none := by decide
example : parse? "#u8(1)" = none := by decide
example : parse? "1+" = none := by decide

/-! ## Printing -/

example : print (ofList [.atom (.keyword "a b"), .cons (.atom .box) (ofList [sym "x"])]) =
    "(#:|a b| #& x)" := by decide

end Silmaril.Formats.Racket
