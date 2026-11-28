module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorCaseOperands.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithLetCase.Defs

/-! # An opt-in typed quotient for administrative returns -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns

open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls
open CategoryTheory

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- The unary-forwarding base already includes returned-call sequencing.
Adjoin constructor beta at primitive operands and the singleton case split. -/
abbrev Step (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  WithUnaryReturns.Step pe Γ r s L ∨
  WithConstructorCaseOperands.Step Γ r s L ∨ WithLetCase.Step Γ r s L

abbrev Eqv := Paper.Extension.Eqv (Step (τ := τ) (Φ := Φ) pe)
abbrev TypeCategory := Paper.Extension.Singleton.TypeCategory (Step (τ := τ) (Φ := Φ) pe)

abbrev projection : Paper.TypeCategory (τ := τ) Φ ⥤ TypeCategory (τ := τ) (Φ := Φ) pe :=
  Paper.Extension.Singleton.projection (Step pe)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns
