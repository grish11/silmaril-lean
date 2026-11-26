module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # Exact graph witnesses for native unary lets -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) {τ : Type u} [TypeFormers τ] (M : TypeModel τ V) {Φ : Type v} [HasTy Φ τ]

/-- A native term let witness exposes its actual intermediate type and both
subterm witnesses. The final result type alone need not determine that type. -/
theorem Denotes.let₁_readback [DistributiveFreydCategory J] [InstructionModel J M Φ]
    {Γ : VCtx τ} {a b : Tm Φ} {B : τ} {h : Tm.HasType Γ (.let₁ a b) B}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj B)} (d : Denotes J M h f) :
    ∃ (A : τ) (hv : Tm.HasType Γ a A) (hb : Tm.HasType (A :: Γ) b B)
      (v : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A))
      (body : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (M.obj B)),
      Denotes J M hv v ∧ Denotes J M hb body ∧ f = bindArrow J v body := by
  cases d with
  | let₁ dv db => exact ⟨_, _, _, _, _, dv, db, rfl⟩

/-- A native region let uses the same value binding while retaining the exact
outward label context of its body. -/
theorem RegionDenotes.let₁_readback [Iteration C] [ElgotCategory C]
    [StrongElgotFreydCategory J] [InstructionModel J M Φ] {Γ : VCtx τ} {L : LCtx τ}
    {a : Tm Φ} {r : Region Φ} {h : Region.HasType Γ (.let₁ a r) L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M h f) :
    ∃ (A : τ) (hv : Tm.HasType Γ a A) (hb : Region.HasType (A :: Γ) r L)
      (v : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A))
      (body : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (labelObj M L)),
      Denotes J M hv v ∧ RegionDenotes J M hb body ∧ f = bindArrow J v body := by
  cases d with
  | let₁ dv db => exact ⟨_, _, _, _, _, dv, db, rfl⟩

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
