module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution

/-! # Precompose a native region witness by a map on its newest input -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Change the newest parameter by a pure typed value map, keeping all older
captures and the original outward label context. -/
theorem RegionDenotes.replaceNewest {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {a : Tm Φ} {A B : τ} {hr : r.HasType (A :: Γ) L}
    {f : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M hr f) {p : M.obj B ⟶ M.obj A} {ha : a.HasType (B :: Γ) A}
    (da : Denotes J M ha (J.map (snd (ctxObj M Γ) (M.obj B) ≫ p))) :
    ∃ ht : (r.substVars (Tm.replaceNewest a)).HasType (B :: Γ) L,
      RegionDenotes J M ht (J.map (ctxObj M Γ ◁ p) ≫ f) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.regionDenotes_replaceNewest J M d da

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
