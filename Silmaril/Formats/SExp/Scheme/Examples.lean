module

public import Silmaril.Formats.SExp.Scheme.Thms

/-! # Scheme (R7RS-small) data: examples, checked by the kernel against the reader -/

namespace Silmaril.Formats.Scheme

open SExp2 SchemeFamily

private def sym (s : String) : Datum := .atom (.symbol s)

/-! ## Accepted -/

example : parse? "(a . b)" = some (.cons (sym "a") (sym "b")) := by decide
example : parse? "(a b . c)" = some (.cons (sym "a") (.cons (sym "b") (sym "c"))) := by decide
example : parse? "(a . (b))" = parse? "(a b)" := by decide
example : parse? "'x" = some (ofList [sym "quote", sym "x"]) := by decide
example : parse? "`(a ,b ,@c)" = parse? "(quasiquote (a (unquote b) (unquote-splicing c)))" := by
  decide
attribute [local cbv_eval] Nat.ofDigitChars_eq_foldl in
example : parse? "#(1 a)" = some (.cons (.atom .vector) (ofList [.atom (.exact 1), sym "a"])) := by
  cbv
/-- A vector and the list of its elements are different data. -/
example : parse? "#(a)" ≠ parse? "(a)" := by decide
attribute [local cbv_eval] Nat.ofDigitChars_eq_foldl in
example : parse? "#u8(0 255)" =
    some (.cons (.atom .bytevector) (ofList [.atom (.exact 0), .atom (.exact 255)])) := by cbv
example : parse? "(#t #false #\\a #\\space #\\( \"s\\n\")" = some (ofList
    [.atom (.boolean true), .atom (.boolean false), .atom (.char 'a'), .atom (.char ' '),
     .atom (.char '('), .atom (.string "s\n")]) := by decide
attribute [local cbv_eval] Nat.ofDigitChars_eq_foldl in
example : parse? "(-12 4/2 1.50 .5 -0.0 1e3)" = some (ofList
    [.atom (.exact (-12)), .atom (.exact 2), .atom (.inexact ⟨false, 150, -2⟩),
     .atom (.inexact ⟨false, 5, -1⟩), .atom (.inexact ⟨true, 0, -1⟩),
     .atom (.inexact ⟨false, 1, 3⟩)]) := by cbv
example : parse? "(+ - ... ->x <=? |a b| a.b)" = some (ofList
    [sym "+", sym "-", sym "...", sym "->x", sym "<=?", sym "a b", sym "a.b"]) := by decide
/-- Identifiers are case-sensitive. -/
example : parse? "(Foo foo)" = some (ofList [sym "Foo", sym "foo"]) := by decide
example : parse? "; c\n #| a #| nested |# b |# (a) ; end" = parse? "(a)" := by decide
example : parsePrefix? "(a) (b)" = some (ofList [sym "a"], " (b)") := by decide

/-! ## Rejected -/

example : parse? "." = none := by decide
example : parse? "(. a)" = none := by decide
example : parse? "(a .)" = none := by decide
example : parse? "(a . b c)" = none := by decide
example : parse? "(a . b . c)" = none := by decide
example : parse? "#(a . b)" = none := by decide
attribute [local cbv_eval] Nat.ofDigitChars_eq_foldl in
example : parse? "#u8(256)" = none := by cbv
attribute [local cbv_eval] Nat.ofDigitChars_eq_foldl in
example : parse? "#u8(a)" = none := by cbv
example : parse? "#;a b" = none := by decide
example : parse? "#0=(a . #0#)" = none := by decide
example : parse? "+inf.0" = none := by decide
example : parse? "#x10" = none := by decide
example : parse? "1+2i" = none := by decide
example : parse? "[a]" = none := by decide
example : parse? "#| unterminated" = none := by decide
example : parse? "(a) (b)" = none := by decide

/-! ## Printing -/

/-- The roundtrip theorem applied to an improper datum with numbers. -/
example : parse? (print (.cons (sym "a b") (.cons (.atom (.exact (-7/2)))
    (.atom (.inexact ⟨false, 15, -1⟩))))) =
    some (.cons (sym "a b") (.cons (.atom (.exact (-7/2))) (.atom (.inexact ⟨false, 15, -1⟩)))) :=
  parse?_print (by decide) (by decide)
attribute [local cbv_eval] Nat.ofDigitChars_eq_foldl in
example : print (.cons (.atom .vector) (ofList [.atom (.char ' '), .atom (.boolean true)])) =
    "#(#\\  #t)" := by cbv

end Silmaril.Formats.Scheme
