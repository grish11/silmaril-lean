module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Freyd.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Chosen.Thms

/-! # Guarded iteration for the structural value inclusion -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.RetainedCase.Chosen (projectedChosenDistributor projectedChosenDistributor_hom)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Comp" => TypeCategory Seed
local notation "Val" => ValueCategory Seed
local notation "ι" => inclusion Seed

attribute [local instance] guardedIteration

/-- The uniformity field for this inclusion uses every structural value map
and the square formed in the actual guarded computation quotient. -/
@[expose] def StructuralUniformity : Prop :=
  ∀ {A D : Val} {B : Comp}
    (f : (ι).obj A ⟶ B ⨿ (ι).obj A) (g : (ι).obj D ⟶ B ⨿ (ι).obj D) (h : A ⟶ D),
    f ≫ coprod.map (𝟙 B) ((ι).map h) = (ι).map h ≫ g →
      CategoryTheory.iterate f = (ι).map h ≫ CategoryTheory.iterate g

variable [Fact (IncludesUnitEta Seed)]

local instance : PremonoidalCategory Comp := computationPremonoidal Seed
local instance : SymmetricPremonoidalCategory Comp := computationSymmetric Seed
noncomputable local instance : DistributivePremonoidalCategory Comp := computationDistributive Seed

/-- The chosen left comparison is the exact guarded distributor transported along the chosen sums. -/
theorem leftIso_eq_guarded (Z B A : Comp) :
    DistributiveTensor.leftIso Z B A = projectedChosenDistributor Seed Z.as B.as A.as := by
  apply Iso.ext
  rw [projectedChosenDistributor_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The chosen guarded iterator satisfies strength for every retained object. -/
theorem iterate_whiskerLeft (Z : Comp) {A B : Comp} (f : A ⟶ B ⨿ A) :
    CategoryTheory.iterate ((Z ◁ f) ≫ DistributivePremonoidalCategory.leftInv Z B A) =
      Z ◁ CategoryTheory.iterate f := by
  change iterateChosen Seed ((whiskerLeftFunctor Seed Z).map f ≫ (DistributiveTensor.leftIso Z B A).inv) =
    (whiskerLeftFunctor Seed Z).map (iterateChosen Seed f)
  rw [leftIso_eq_guarded Seed Z B A]
  exact whiskerLeft_iterateChosen Seed (show τ from Z.as) f

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues
