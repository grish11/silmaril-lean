module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorCaseOperands.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands.Soundness

/-! # Structural and contextual soundness of constructor beta in a call operand -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorCaseOperands

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem OperandBeta.typed {Γ : VCtx τ} {a b : Tm Φ} {D : τ} (h : OperandBeta Γ a b D) :
    Tm.HasType Γ a D ∧ Tm.HasType Γ b D :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands.operand_typed h

theorem Step.valueBranches {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Step Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands.step_branches h

theorem Step.replay {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Step Γ r s L) :
    Eqv Γ r s L :=
  .extra h.valueBranches.1.hasType h.valueBranches.2.hasType h

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) (M : TypeModel τ V) [InstructionModel J M Φ]

/-- A known left constructor runs its payload once before the corresponding arm. -/
theorem inl_denotes_bind [DistributiveFreydCategory J] {Γ : VCtx τ} {a l r : Tm Φ} {A B D : τ}
    {ha : Tm.HasType Γ a A} {hl : Tm.HasType (A :: Γ) l D}
    {hr : Tm.HasType (B :: Γ) r D}
    {fa : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    {fl : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (M.obj D)}
    {fr : J.obj (ctxObj M (B :: Γ)) ⟶ J.obj (M.obj D)}
    (da : Denotes J M ha fa) (dl : Denotes J M hl fl) (dr : Denotes J M hr fr) :
    Denotes J M (.case (.inl ha) hl hr)
      (Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J fa fl) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands.inl_denotes_bind J M da dl dr

/-- A known right constructor runs its payload once before the corresponding arm. -/
theorem inr_denotes_bind [DistributiveFreydCategory J] {Γ : VCtx τ} {a l r : Tm Φ} {A B D : τ}
    {ha : Tm.HasType Γ a B} {hl : Tm.HasType (A :: Γ) l D}
    {hr : Tm.HasType (B :: Γ) r D}
    {fa : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj B)}
    {fl : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (M.obj D)}
    {fr : J.obj (ctxObj M (B :: Γ)) ⟶ J.obj (M.obj D)}
    (da : Denotes J M ha fa) (dl : Denotes J M hl fl) (dr : Denotes J M hr fr) :
    Denotes J M (.case (.inr ha) hl hr)
      (Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J fa fr) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands.inr_denotes_bind J M da dl dr

/-- Both typed operands have a common structural arrow. The pure payload is
substituted into the chosen arm with its original captures, and the arm
itself may denote an arbitrary computation. -/
theorem OperandBeta.denotes [DistributiveFreydCategory J] {Γ : VCtx τ} {a b : Tm Φ} {D : τ}
    (h : OperandBeta Γ a b D) (ha : Tm.HasType Γ a D) (hb : Tm.HasType Γ b D) :
    ∃ f, Denotes J M ha f ∧ Denotes J M hb f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands.operand_denotes J M h ha hb

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

/-- The root-region witness uses the same primitive and the same outward
continuations on both sides. -/
theorem step_denotes : Paper.Extension.Singleton.SeedDenotes (Seed := Step (Φ := Φ)) J M :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands.step_denotes J M

variable [RegionTypingCoherent (Φ := Φ) J M] [FreydCategory.CentralUnit J]
  (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
    Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)

include shared in
/-- The seed lifts to the typed contextual closure in the existing Paper model class. -/
theorem Eqv.sound {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Paper.Extension.Eqv.sound J M shared (step_denotes (Φ := Φ) J M) h hr hs

/-- The categorical denotation of the opt-in singleton quotient. -/
@[expose] noncomputable def denoteFunctor :
    Paper.Extension.Singleton.TypeCategory (Step (τ := τ) (Φ := Φ)) ⥤ C :=
  Paper.Extension.Singleton.denoteFunctor J M shared (step_denotes (Φ := Φ) J M)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorCaseOperands
