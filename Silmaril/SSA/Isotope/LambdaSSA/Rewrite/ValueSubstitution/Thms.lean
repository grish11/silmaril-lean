module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.BranchValues

/-! # Simultaneous transport along constructor-valued substitutions -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits

open CartesianMonoidalCategory (fst)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

section Term

variable (J : V ⥤ C) [DistributiveFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Weakening an expression by a fresh captured value precomposes its denotation by projection. -/
theorem Denotes.weaken {Γ : VCtx τ} {A : τ} {a : Tm Φ} {ha : Tm.HasType Γ a A}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)} (d : Denotes J M ha f) (B : τ) :
    Denotes J M (ha.rename (Ren.wk Γ B)) (J.map (fst (ctxObj M Γ) (M.obj B)) ≫ f) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.denotes_rename J M d (Ren.wk Γ B) (fun _ _ _ => rfl)

/-- Substituting a payload with a named pure map retains the original captures
and precomposes the selected term by pairing them with that payload. -/
theorem Denotes.substValue {Γ : VCtx τ} {a b : Tm Φ} {A B : τ}
    {ha : Tm.HasType Γ a A} {hb : Tm.HasType (A :: Γ) b B}
    {p : ctxObj M Γ ⟶ M.obj A} {f : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (M.obj B)}
    (da : Denotes J M ha (J.map p)) (db : Denotes J M hb f) :
    ∃ hs : Tm.HasType Γ (b.subst (Tm.singleSubst a)) B,
      Denotes J M hs (J.map (CartesianMonoidalCategory.lift (𝟙 _) p) ≫ f) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.denotes_substValue J M da db

end Term

variable [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Constructor-valued substitution precomposes every region arrow by the
same value map for the given substitution. -/
theorem RegionDenotes.substBranchValues {Γ Δ : VCtx τ} {σ : Nat → Tm Φ}
    (hσ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (σ i) A) :
    ∃ k : ctxObj M Δ ⟶ ctxObj M Γ,
      ∀ {L : LCtx τ} {r : Region Φ} {hr : Region.HasType Γ r L}
        {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)},
        RegionDenotes J M hr f →
          ∃ ht : Region.HasType Δ (r.substVars σ) L, RegionDenotes J M ht (J.map k ≫ f) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.substBranchValues J M hσ

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
