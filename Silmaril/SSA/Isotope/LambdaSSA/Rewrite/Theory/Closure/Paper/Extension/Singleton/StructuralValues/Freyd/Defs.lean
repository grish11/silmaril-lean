module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Products.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

/-! # Chosen structures for the guarded structural value inclusion -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

abbrev ofSyntaxType (A : τ) : ValueCategory Seed := ⟨ofType Seed A⟩

/-- The selected seed contains the guarded unit-η equation. -/
abbrev IncludesUnitEta : Prop :=
  ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L

variable [unitEta : Fact (IncludesUnitEta Seed)]

/-- Use the guarded syntax unit and products. -/
noncomputable abbrev valueCartesian : CartesianMonoidalCategory (ValueCategory Seed) :=
  cartesian Seed unitEta.out

noncomputable local instance : CartesianMonoidalCategory (ValueCategory Seed) :=
  valueCartesian Seed

noncomputable abbrev valueBraided : BraidedCategory (ValueCategory Seed) :=
  BraidedCategory.ofCartesianMonoidalCategory

abbrev computationPremonoidal : PremonoidalCategory (TypeCategory Seed) :=
  premonoidalOfUnitEta Seed unitEta.out

abbrev computationSymmetric :
    @SymmetricPremonoidalCategory (TypeCategory Seed) _ (computationPremonoidal Seed) :=
  symmetricPremonoidalOfUnitEta Seed unitEta.out

attribute [local instance] hasFiniteCoproducts

/-- The type model chooses the guarded syntax objects, with the canonical chosen-sum comparison. -/
@[instance_reducible] noncomputable def typeModel : TypeModel τ (ValueCategory Seed) where
  obj := ofSyntaxType Seed
  productIso _ _ := Iso.refl _
  unitIso := Iso.refl _
  coprodIso A B := (sumIsColimit Seed A B).coconePointUniqueUpToIso (colimit.isColimit _)
  emptyIsInitial := emptyIsInitial Seed

/-- Use the projected guarded primitive return for each instruction. -/
@[instance_reducible] def instructions : InstructionModel (inclusion Seed) (typeModel Seed) Φ where
  denote p := (projection Seed).map (Paper.TypeCategory.primitiveReturn p)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues
