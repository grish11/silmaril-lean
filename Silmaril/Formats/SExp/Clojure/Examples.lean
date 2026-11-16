module

public import Silmaril.Formats.SExp.Clojure.Thms
-- Some definitions the Clojure reader evaluates (decimal digit folds in `Init`) are not
-- exposed to the kernel otherwise.
import all Init.Data.Nat.ToString

/-! # Clojure data syntax: examples

Each example is checked by the kernel (`decide`) against the executable reader. -/

namespace Silmaril.Formats.Clojure

open SExp2

private def s (n : String) : Datum := .atom (.symbol none n)
private def kw (n : String) : Datum := .atom (.keyword none n)
private def int (n : Int) : Datum := .atom (.integer n false)

/-! ## Collections keep their syntax -/

example : parse? "(a b)" = some (ofList [s "a", s "b"]) := by decide +kernel
example : parse? "[a b]" = some (.cons (.atom .vector) (ofList [s "a", s "b"])) := by decide +kernel
example : parse? "{a b}" = some (.cons (.atom .map) (ofList [s "a", s "b"])) := by decide +kernel
example : parse? "#{a b}" = some (.cons (.atom .set) (ofList [s "a", s "b"])) := by decide +kernel
/-- The four collection kinds are pairwise distinct. -/
example : [parse? "(a b)", parse? "[a b]", parse? "{a b}", parse? "#{a b}"].Nodup := by decide +kernel
/-- `nil` is a literal, not the empty list. -/
example : parse? "nil" = some (.atom .nil) ∧ parse? "()" = some .nil := by decide +kernel
/-- No dotted pairs: `.` is a symbol. -/
example : parse? "(a . b)" = some (ofList [s "a", s ".", s "b"]) := by decide +kernel
example : parse? "{:a 1, :b [2 3]}" =
    some (.cons (.atom .map) (ofList [kw "a", int 1, kw "b",
      .cons (.atom .vector) (ofList [int 2, int 3])])) := by decide +kernel

/-! ## Atoms -/

/-- Long, BigInt, double and BigDecimal literals of the value one are distinct atoms. -/
example : [parse? "1", parse? "1N", parse? "1.0", parse? "1M"].Nodup := by decide +kernel
example : parse? "9223372036854775808" = some (.atom (.integer (2 ^ 63) true)) := by decide +kernel
example : parse? "-1.5e3" = some (.atom (.float ⟨true, 15, 2⟩ false)) := by decide +kernel
example : parse? "(\\a \\newline \\( \"x\\ty\")" =
    some (ofList [.atom (.char 'a'), .atom (.char '\n'), .atom (.char '('),
      .atom (.string "x\ty")]) := by decide +kernel
example : parse? "clojure.core/map" = some (.atom (.symbol (some "clojure.core") "map")) := by
  decide +kernel
example : parse? ":ns/k" = some (.atom (.keyword (some "ns") "k")) := by decide +kernel
example : parse? "a'b" = some (s "a'b") := by decide +kernel
/-- Abbreviations read as their longhand lists. -/
example : parse? "'x" = some (ofList [s "quote", s "x"]) := by decide +kernel
example : parse? "@x" = parse? "(clojure.core/deref x)" := by decide +kernel
example : parse? "#'x" = parse? "(var x)" := by decide +kernel
example : parse? "~@x" = parse? "(clojure.core/unquote-splicing x)" := by decide +kernel
/-- Commas are whitespace; `;` starts a comment. -/
example : parse? "[1,2 ,3] ; done" = parse? "[1 2 3]" := by decide +kernel
example : parsePrefix? "[a] b" = some (.cons (.atom .vector) (ofList [s "a"]), " b") := by
  decide +kernel

/-! ## Rejected -/

example : parse? "{:a}" = none := by decide +kernel
example : parse? "{:a 1 :a 2}" = none := by decide +kernel
example : parse? "#{1 1}" = none := by decide +kernel
example : parse? "`a" = none := by decide +kernel
example : parse? "^:m a" = none := by decide +kernel
example : parse? "#(inc %)" = none := by decide +kernel
example : parse? "#_a b" = none := by decide +kernel
example : parse? "#\"re\"" = none := by decide +kernel
example : parse? "#inst \"2020\"" = none := by decide +kernel
example : parse? "::k" = none := by decide +kernel
example : parse? "012" = none := by decide +kernel
example : parse? "0x1F" = none := by decide +kernel
example : parse? "1/2" = none := by decide +kernel
example : parse? "\\u0041" = none := by decide +kernel
example : parse? "(a" = none := by decide +kernel
example : parse? "[a)" = none := by decide +kernel
example : parse? "a b" = none := by decide +kernel

/-! ## Printing -/

example : print (.cons (.atom .set) (ofList [kw "a", .atom (.float ⟨false, 15, -1⟩ true),
    .atom (.char ' '), .atom (.integer 7 true), s "/"])) =
    "#{:a 15e-1M \\space 7N /}" := by decide +kernel

end Silmaril.Formats.Clojure
