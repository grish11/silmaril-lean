module

public import Mathlib.SetTheory.ZFC.Basic
public import Silmaril.Logic.SetTheory.Nat

@[expose] public section

/-! # Explicit tagged constructor values for concrete CIC inductive interpretations -/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

/-- An ordered tuple of constructor argument values, with a distinct empty code. -/
def argumentTuple : List ZFSet.{u} → ZFSet.{u}
  | [] => ∅
  | value :: values => ZFSet.pair value (argumentTuple values)

/-- A constructor is represented by its natural-number tag and its actual argument tuple. -/
def constructorValue (index : ℕ) (arguments : List ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair (Silmaril.Logic.SetTheory.numeral index) (argumentTuple arguments)

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
