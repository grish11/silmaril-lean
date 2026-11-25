module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming

/-! # Categorical naturality of exact λSSA under label renaming -/

public section

universe v₁ v₂ u₁ u₂ w q

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

section Labels

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V]
  [HasFiniteCoproducts V] {τ : Type w} [TypeFormers τ] (M : TypeModel τ V)

/-- The action of a label renaming on an individual exit injection. -/
@[reassoc]
theorem labelInject_labelMap {L K : LCtx τ} {ρ : Nat → Nat} (hρ : Ren L K ρ)
    {i : Nat} {A : τ} (hi : At L i A) :
    labelInject M i hi ≫ labelMap M hρ = labelInject M (ρ i) (hρ hi) :=
  labelInject_labelMap_proof M hρ hi

@[simp]
theorem labelMap_id (L : LCtx τ) :
    labelMap M (SSA.Ren.id L) = 𝟙 (labelObj M L) :=
  labelMap_id_proof M L

theorem labelMap_comp {L K H : LCtx τ} {ρ σ : Nat → Nat}
    (hρ : Ren L K ρ) (hσ : Ren K H σ) :
    labelMap M (SSA.Ren.comp hρ hσ) = labelMap M hρ ≫ labelMap M hσ :=
  labelMap_comp_proof M hρ hσ

end Labels

section Region

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type w} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type q} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Renaming the outward labels of a region postcomposes its denotation with the
corresponding value map. Locally bound CFG labels remain fixed. -/
theorem RegionDenotes.renameLabels {Γ : VCtx τ} {L K : LCtx τ} {ρ : Nat → Nat}
    {r : Region Φ} {hr : Region.HasType Γ r L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M hr f) (hρ : Ren L K ρ) :
    RegionDenotes J M (hr.renameLabels hρ) (f ≫ J.map (labelMap M hρ)) :=
  RegionDenotes.renameLabels_proof J M d hρ

/-- The corresponding equality of the chosen region arrows in a coherent model. -/
theorem denoteRegion_renameLabels [RegionTypingCoherent (Φ := Φ) J M]
    {Γ : VCtx τ} {L K : LCtx τ} {ρ : Nat → Nat}
    {r : Region Φ} (hr : Region.HasType Γ r L) (hρ : Ren L K ρ) :
    denoteRegion J M (hr.renameLabels hρ) =
      denoteRegion J M hr ≫ J.map (labelMap M hρ) :=
  (RegionDenotes.eq_denote J M (RegionDenotes.renameLabels J M (denoteRegion_spec J M hr) hρ)).symm

end Region

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
