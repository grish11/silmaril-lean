module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Freyd.Iteration.Thms

/-! # The structural value embedding of the ordered-pair join -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues

open CategoryTheory

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)

open Extension.Singleton.StructuralValues (IncludesUnitEta)
local notation "Seed" => JoinedStep (τ := τ) (Φ := Φ) pe

instance unitEta : Fact (IncludesUnitEta (Seed)) :=
  ⟨fun h => .inl (.inl (.inr h))⟩

/-- The Cartesian structural values embed distributively into the ordered-pair computations. -/
noncomputable abbrev distributiveFreyd :=
  Extension.Singleton.StructuralValues.distributiveFreyd (Seed)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues
