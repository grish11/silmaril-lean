module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Term.Defs

/-! # A unary-return body under an exact product destructure -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.Example

open Silmaril Silmaril.Isotope.LambdaSSA

universe u v

abbrev U (α : Type u) : Ty α := .unit

/-- Bind and return the pair rebuilt from the two opened fields. -/
def body {Φ : Type v} : Tm Φ :=
  .let₁ (.pair (.var 1) (.var 0)) (.var 0)

theorem body_typed {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] :
    Tm.HasType [U α, U α] (body : Tm Φ) (product (U α) (U α)) :=
  .let₁ (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)) (.var (i := 0) rfl)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.Example
