module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

/-! # Selected denotations under singleton value substitution -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Singleton

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem regionDenotes_substSingleton {Δ : VCtx τ} {L : LCtx τ} {X : τ} {r : Region Φ}
    {hr : Region.HasType [X] r L} {f : J.obj (ctxObj M [X]) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M hr f) (σ : Nat → Tm Φ)
    {hv : Tm.HasType Δ (σ 0) X} {v : ctxObj M Δ ⟶ M.obj X}
    (dv : Denotes J M hv (J.map v)) :
    ∃ h : Region.HasType Δ (r.substVars σ) L,
      RegionDenotes J M h (J.map (v ≫ (λ_ (M.obj X)).inv) ≫ f) := by
  have hσ : SubstDenotes J M (Γ := [X]) σ (v ≫ (λ_ (M.obj X)).inv) := by
    intro i A h
    cases i with
    | zero =>
      cases Option.some.inj h
      refine ⟨hv, ?_⟩
      simpa only [Category.assoc, lookup, ctxObj, ← CartesianMonoidalCategory.leftUnitor_hom,
        Iso.inv_hom_id, Category.comp_id] using dv
    | succ i => simp [At] at h
  exact regionDenotes_subst J M d hσ

set_option backward.isDefEq.respectTransparency false in
theorem denotes_subst {Δ : VCtx τ} {X D : τ} {t : Tm Φ} {ht : Tm.HasType [X] t D}
    {f : J.obj (ctxObj M [X]) ⟶ J.obj (M.obj D)} (d : Denotes J M ht f)
    (σ : Nat → Tm Φ) {hv : Tm.HasType Δ (σ 0) X} {v : ctxObj M Δ ⟶ M.obj X}
    (dv : Denotes J M hv (J.map v)) :
    ∃ h : Tm.HasType Δ (t.subst σ) D,
      Denotes J M h (J.map (v ≫ (λ_ (M.obj X)).inv) ≫ f) := by
  let hi : At [D] 0 D := rfl
  -- Substitute under a singleton branch, then recover the term arrow by decoding the exit.
  obtain ⟨ht', dt⟩ := regionDenotes_substSingleton J M (RegionDenotes.br (h := hi) d) σ dv
  change Region.HasType Δ (.br 0 (t.subst σ)) [D] at ht'
  generalize he : J.map (v ≫ (λ_ (M.obj X)).inv) ≫ (f ≫ J.map (labelInject M 0 hi)) = combined at dt
  cases dt with
  | br da =>
    rename_i A _ _ hA
    have eqType : D = A := Option.some.inj hA
    subst A
    have cancel := congrArg (· ≫ J.map (singletonLabelPayload M D)) he
    simp only [Category.assoc, ← J.map_comp] at cancel
    have strip (h : At [D] 0 D) : labelInject M 0 h ≫ singletonLabelPayload M D = 𝟙 _ :=
      SingletonDispatcher.labelInject_payload M D
    simp only [strip, J.map_id, Category.comp_id] at cancel
    exact ⟨_, cancel.symm ▸ da⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Singleton
