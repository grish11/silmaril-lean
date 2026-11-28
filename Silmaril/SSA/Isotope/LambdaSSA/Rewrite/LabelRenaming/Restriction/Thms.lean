module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming

/-! # Read an exact witness back through an outward label renaming -/

public section

universe v₁ v₂ u₁ u₂ w q

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

/-- Compare pure label arrows on the exact typed injections. -/
theorem labelHom_ext {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V]
    [HasFiniteCoproducts V] {τ : Type w} [TypeFormers τ] (M : TypeModel τ V)
    {L : LCtx τ} {Y : V} {f g : labelObj M L ⟶ Y}
    (h : ∀ (i : Nat) (A : τ) (hi : At L i A), labelInject M i hi ≫ f = labelInject M i hi ≫ g) :
    f = g :=
  labelHom_ext_proof M h

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

open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop)

/-- Outward payload maps pass through a native dispatcher. The entry and
step keep their recursive summands, so this uses ordinary Elgot naturality. -/
theorem cfgDispatch_postmap {E A B D : V} (out : B ⟶ D)
    (entry : J.obj E ⟶ J.obj (B ⨿ A)) (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) :
    caseWithContext J (entry ≫ J.map (coprod.map out (𝟙 A))) (J.map (snd E D))
      (contextualLoop J (body ≫ J.map (coprod.map out (𝟙 A)))) =
    caseWithContext J entry (J.map (snd E B)) (contextualLoop J body) ≫ J.map out :=
  cfgDispatch_postmap_proof J out entry body

/-- If the smaller region's written targets fit its label context, any
exact witness of its outward renaming factors through an exact witness
of the smaller region. The proof keeps each selected internal family
and uses outward naturality of iteration at nested CFGs. -/
theorem RegionDenotes.of_renameLabels {Γ : VCtx τ} {L K : LCtx τ} {ρ : Nat → Nat}
    {r : Region Φ} (scope : r.LabelsBound L.length) (hρ : Ren L K ρ)
    {hr : Region.HasType Γ (r.renameLabels ρ) K}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M K)}
    (d : RegionDenotes J M hr f) :
    ∃ (ht : r.HasType Γ L) (g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)),
      RegionDenotes J M ht g ∧ f = g ≫ J.map (labelMap M hρ) :=
  RegionDenotes.of_renameLabels_proof J M scope hρ d

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
