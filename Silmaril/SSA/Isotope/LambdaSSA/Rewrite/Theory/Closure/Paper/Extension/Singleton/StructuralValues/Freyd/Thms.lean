module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Freyd.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValueFreyd

/-! # The guarded structural value inclusion is distributive Freyd -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.RetainedCase (distributorIso)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  [unitEta : Fact (IncludesUnitEta Seed)]

local notation "Val" => ValueCategory Seed
local notation "Comp" => TypeCategory Seed
local notation "ι" => inclusion Seed

noncomputable local instance : CartesianMonoidalCategory Val := valueCartesian Seed
noncomputable local instance : BraidedCategory Val := valueBraided Seed
local instance : PremonoidalCategory Comp := computationPremonoidal Seed
local instance : SymmetricPremonoidalCategory Comp := computationSymmetric Seed
attribute [local instance] hasFiniteCoproducts preservesFiniteCoproducts

include unitEta in
/-- The inverse of a structural isomorphism in the computation quotient is structural. -/
theorem iso_inv_mem {A B : Comp} (e : A ≅ B) (h : HomProperty Seed e.hom) :
    HomProperty Seed e.inv :=
  StructuralValueFreyd.iso_inv_mem Seed e h

local infixr:70 " ×ₜ " => Silmaril.product
local infixr:65 " ⊕ₜ " => Silmaril.coprod

include unitEta in
/-- The guarded distributor lifts to an isomorphism of structural values. -/
noncomputable def distributor (X A B : τ) :
    ofSyntaxType Seed ((X ×ₜ A) ⊕ₜ (X ×ₜ B)) ≅ ofSyntaxType Seed (X ×ₜ (A ⊕ₜ B)) :=
  StructuralValueFreyd.distributor Seed X A B

/-- The lift uses the literal projected guarded distributor in both directions. -/
theorem inclusion_mapIso_distributor (X A B : τ) :
    (ι).mapIso (distributor Seed X A B) =
      ((projection Seed).mapIso (distributorIso X A B)).symm :=
  StructuralValueFreyd.inclusion_mapIso_distributor Seed X A B

/-- Fixed-left tensor sends the exact value sum to a coproduct. -/
noncomputable def whiskeredSumIsColimit (X A B : τ) :
    IsColimit (BinaryCofan.map (MonoidalCategory.tensorLeft (ofSyntaxType Seed X)) (sum Seed A B)) :=
  StructuralValueFreyd.whiskeredSumIsColimit Seed X A B

theorem valueDistributive : DistributiveTensor Val :=
  StructuralValueFreyd.valueDistributive Seed

theorem computationDistributive : DistributivePremonoidalCategory Comp :=
  StructuralValueFreyd.computationDistributive Seed

/-- Cartesian pairing in the value category is the guarded pair in computations. -/
theorem inclusion_map_lift {X A B : τ}
    (f : ofSyntaxType Seed X ⟶ ofSyntaxType Seed A) (g : ofSyntaxType Seed X ⟶ ofSyntaxType Seed B) :
    (ι).map (CartesianMonoidalCategory.lift f g) = pairArrows Seed f.hom g.hom :=
  StructuralValueFreyd.map_lift Seed f g

/-- The structural inclusion preserves unit and tensor with identity comparisons. -/
@[instance_reducible] noncomputable def freyd : FreydCategory (ι) :=
  StructuralValueFreyd.freyd Seed

noncomputable local instance : DistributiveTensor Val := valueDistributive Seed
noncomputable local instance : DistributivePremonoidalCategory Comp := computationDistributive Seed

/-- The inclusion is distributive Freyd for the guarded products, sums, and tensor. -/
@[instance_reducible] noncomputable def distributiveFreyd : DistributiveFreydCategory (ι) where
  toFreydCategory := freyd Seed
  preservesFiniteCoproducts := inferInstance

/-- The distributive structure retains the chosen Freyd structure. -/
theorem distributiveFreyd_toFreydCategory :
    (distributiveFreyd Seed).toFreydCategory = freyd Seed := by
  unfold distributiveFreyd
  rfl

theorem centralUnit :
    letI := freyd Seed
    FreydCategory.CentralUnit (ι) :=
  StructuralValueFreyd.centralUnit Seed

theorem sharedTensor (X Y : Val) :
    letI := freyd Seed
    ∃ h : (ι).obj X ⊗ (ι).obj Y = (ι).obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := (ι)) X Y = eqToIso h :=
  StructuralValueFreyd.sharedTensor Seed X Y

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues
