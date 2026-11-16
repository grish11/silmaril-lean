module

public import Silmaril.Logic.Kore.FixedPoint.Examples

@[expose] public section
namespace Silmaril.Logic.Kore.FixedPoint.Examples

/-- Negative set occurrences are outside this positive fragment. -/
theorem negative_rejected : (Syntax.parse "\\mu{}(@X:S{},\\not{S{}}(@X:S{}))").isNone = true := by decide

theorem wrong_binder_sort_rejected :
    (Checking.read scope 20 [] [] "S" "\\mu{}(@X:S{},@X:T{})").isNone = true := by decide

theorem nearest_wrong_sort_rejected :
    (Checking.read scope 20 [("@X", "S")] [] "T"
      "\\nu{}(@X:T{},lift{}(@X:S{}))").isNone = true := by decide

theorem unknown_set_rejected :
    (Checking.read scope 20 [] [] "S" "@X:S{}").isNone = true := by decide

theorem unknown_symbol_rejected :
    (Checking.read scope 20 [] [] "S" "missing{}()").isNone = true := by decide

theorem malformed_set_rejected : (Syntax.parse "@0:S{}").isNone = true := by decide

theorem wrong_arity_rejected :
    (Checking.read scope 20 [] [] "S" "step{}()").isNone = true := by decide

theorem unsupported_rejected : (Syntax.parse "\\next{S{}}(\\top{S{}}())").isNone = true := by decide

theorem trailing_rejected : (Syntax.parse "\\top{S{}}() seed{}()").isNone = true := by decide

/-- Equal textual stems inhabit separate element/set namespaces. -/
theorem separate_namespaces :
    Checking.read scope 20 [("@X", "S")] [("X", "S")] "S" "\\and{S{}}(X:S{},@X:S{})" =
      some (.conj (.base (.var 0)) (.setvar 0)) := by rfl

/-- Quantifier binding preserves the set variable; mixed sorts are accepted
when the bound element's own sort is declared. -/
theorem mixed_quantifier_accepted :
    (Checking.read scope 20 [("@X", "S")] [] "S"
      "\\exists{S{}}(x:T{},\\and{S{}}(@X:S{},\\top{S{}}()))").isSome = true := by decide
theorem binary_symbol_accepted :
    (Checking.read scope 20 [] [] "S" "pair{}(seed{}(),seed{}())").isSome = true := by decide
end Silmaril.Logic.Kore.FixedPoint.Examples
