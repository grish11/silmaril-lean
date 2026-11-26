module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Thms

/-! # The structural value embedding after adding product-variable return fusion -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.StructuralValues

open CategoryTheory

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)

open Extension.Singleton.StructuralValues (IncludesUnitEta)
local notation "Seed" => JoinedStep (τ := τ) (Φ := Φ) pe

instance unitEta : Fact (IncludesUnitEta (Seed)) :=
  ⟨fun h => .inl (.inl ((WithPairReturns.StructuralValues.unitEta (Φ := Φ) pe).out h))⟩

/-- The same guarded products, sums, and tensor supply a distributive Freyd embedding. -/
noncomputable abbrev distributiveFreyd :=
  Extension.Singleton.StructuralValues.distributiveFreyd (Seed)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.StructuralValues
