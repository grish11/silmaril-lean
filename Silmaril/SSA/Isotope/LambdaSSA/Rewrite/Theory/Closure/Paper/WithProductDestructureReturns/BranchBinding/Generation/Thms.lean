module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.BranchBinding.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Generation.Thms

/-! # Literal raw generation for the product-destructuring representative grammar -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.BranchBinding

open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding
open CfgEta.TypeCategory (returnRegion_typed)
open Paper.PackedBody (applyPackedTerm_typed)
open Paper.RetainedLet (unpackTerm_typed)
open Paper.WithPairReturns (ReturnFragmentWithRules)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "S" => singletonSeed (τ := τ) (Φ := Φ) pe

/-- A certified guarded representative generates its literal raw class in the
product-destructuring join. The certificate ranges over the guarded syntax grammar. -/
theorem raw_generated_guardedFragment {X D : τ} {r : Region Φ} {hr : ValueBranches [X] r [D]}
    (h : GuardedFragment pe hr) :
    Singleton.Generation.Generated S (Singleton.rawClass S hr.hasType) :=
  (Singleton.Generation.generated_rawClass_iff S hr).mpr (generated_guardedFragment pe h)

/-- The returned destructure on the input product variable belongs to the raw
generated domain whenever its packed body has the extended return certificate. -/
theorem raw_generated_returned_destructure {X A D : τ} {c : Tm Φ}
    {hc : Tm.HasType [product X A] c D} (h : ReturnFragmentWithRules pe true true hc) :
    Singleton.Generation.Generated S (Singleton.rawClass S
      (returnRegion_typed (unpackTerm_typed (applyPackedTerm_typed hc))).hasType) :=
  raw_generated_guardedFragment pe (.returned (.destructure rfl h))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.BranchBinding
