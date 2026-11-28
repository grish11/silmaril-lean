module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithCaseBind

/-! # Soundness and contextual use of the case-to-bind conversion -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind

open Silmaril CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.Extension.Singleton (SeedDenotes)
open RetainedCase (boundCase)
open CfgEta.TypeCategory (returnRegion)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Replay the conversion in an extension that includes this seed. -/
theorem case_eq_let {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (includeBind : ∀ {Γ L r s}, Step Γ r s L → Seed Γ r s L)
    {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {l r : Region Φ}
    (ha : Tm.HasType Γ a (coprod A B)) (hl : ValueBranches (A :: Γ) l L)
    (hr : ValueBranches (B :: Γ) r L) :
    Extension.Eqv Seed Γ (.case a l r) (.let₁ a (boundCase l r)) L :=
  let e := Step.bind ha hl hr
  .extra e.valueBranches.1.hasType e.valueBranches.2.hasType (includeBind e)

/-- The case continues from the usual lowered return of its discriminator.
The continuation takes the retained input and the sum from that single evaluation. -/
theorem case_eq_return_post {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (bind : ∀ {Γ L r s}, Step Γ r s L → Seed Γ r s L)
    (unary : ∀ {Γ L r s}, Paper.UnaryReturn.Step Γ r s L → Seed Γ r s L)
    {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {l r : Region Φ}
    (ha : Tm.HasType Γ a (coprod A B)) (hl : ValueBranches (A :: Γ) l L)
    (hr : ValueBranches (B :: Γ) r L) :
    Extension.Eqv Seed Γ (.case a l r) ((returnRegion a).lsubst (fun _ => boundCase l r)) L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithCaseBind.case_eq_return_post bind unary ha hl hr

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The converted case computes the same arrow at every exact typing. -/
theorem step_denotes : SeedDenotes (Seed := Step (τ := τ) (Φ := Φ)) J M :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithCaseBind.step_denotes J M

/-- Soundness of any supplied seed extends to its case-binding join. -/
theorem joined_seedDenotes {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (base : SeedDenotes (Seed := Seed) J M) :
    SeedDenotes (Seed := JoinedStep Seed) J M :=
  fun e hr hs => e.elim (fun h => base h hr hs) (fun h => step_denotes J M h hr hs)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind
