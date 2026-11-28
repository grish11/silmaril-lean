module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.ProductLet.Defs

/-! # Exact graph witnesses for native product lets -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) {τ : Type u} [TypeFormers τ] (M : TypeModel τ V) {Φ : Type v} [HasTy Φ τ]

omit [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C] in
/-- Postcomposition acts on the body of the product let. -/
theorem bindProduct_postcomp [FreydCategory J] {Γ : VCtx τ} {A B : τ} {X Y : V}
    (value : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (Silmaril.product A B)))
    (body : J.obj (ctxObj M (B :: A :: Γ)) ⟶ J.obj X) (k : J.obj X ⟶ J.obj Y) :
    bindProduct J M value body ≫ k = bindProduct J M value (body ≫ k) := by
  simp only [bindProduct, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    Category.assoc]

/-- Read back both component types from an arbitrary native term witness. -/
theorem Denotes.let₂_readback [DistributiveFreydCategory J] [InstructionModel J M Φ]
    {Γ : VCtx τ} {a b : Tm Φ} {D : τ} {h : Tm.HasType Γ (.let₂ a b) D}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj D)} (d : Denotes J M h f) :
    ∃ (A B : τ) (hv : a.HasType Γ (Silmaril.product A B)) (hb : b.HasType (B :: A :: Γ) D)
      (v : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (Silmaril.product A B)))
      (body : J.obj (ctxObj M (B :: A :: Γ)) ⟶ J.obj (M.obj D)),
      Denotes J M hv v ∧ Denotes J M hb body ∧ f = bindProduct J M v body := by
  cases d with
  | let₂ dv db => exact ⟨_, _, _, _, _, _, dv, db, rfl⟩

/-- Read back both component types and the original label context of an
arbitrary native region witness. -/
theorem RegionDenotes.let₂_readback [Iteration C] [ElgotCategory C]
    [StrongElgotFreydCategory J] [InstructionModel J M Φ] {Γ : VCtx τ} {L : LCtx τ}
    {a : Tm Φ} {r : Region Φ} {h : Region.HasType Γ (.let₂ a r) L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M h f) :
    ∃ (A B : τ) (hv : a.HasType Γ (Silmaril.product A B)) (hb : r.HasType (B :: A :: Γ) L)
      (v : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (Silmaril.product A B)))
      (body : J.obj (ctxObj M (B :: A :: Γ)) ⟶ J.obj (labelObj M L)),
      Denotes J M hv v ∧ RegionDenotes J M hb body ∧ f = bindProduct J M v body := by
  cases d with
  | let₂ dv db => exact ⟨_, _, _, _, _, _, dv, db, rfl⟩

/-- A determined product initializer fixes both binders of the actual graph. -/
theorem RegionDenotes.let₂_readback_at [Iteration C] [ElgotCategory C]
    [StrongElgotFreydCategory J] {κ : Type u} (N : TypeModel (Ty κ) V)
    {Ψ : Type v} [HasTy Ψ (Ty κ)] [InstructionModel J N Ψ]
    {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {a : Tm Ψ} {r : Region Ψ} {A B : Ty κ}
    (fixed : TypeDetermined Γ a (.product A B)) {h : Region.HasType Γ (.let₂ a r) L}
    {f : J.obj (ctxObj N Γ) ⟶ J.obj (labelObj N L)} (d : RegionDenotes J N h f) :
    ∃ (hv : a.HasType Γ (.product A B)) (hb : r.HasType (B :: A :: Γ) L)
      (v : J.obj (ctxObj N Γ) ⟶ J.obj (N.obj (.product A B)))
      (body : J.obj (ctxObj N (B :: A :: Γ)) ⟶ J.obj (labelObj N L)),
      Denotes J N hv v ∧ RegionDenotes J N hb body ∧ f = bindProduct J N v body := by
  obtain ⟨D, E, hv, hb, v, body, dv, db, eq⟩ := d.let₂_readback J N
  obtain ⟨rfl, rfl⟩ := Ty.product.inj (fixed (.product D E) hv)
  exact ⟨hv, hb, v, body, dv, db, eq⟩

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
