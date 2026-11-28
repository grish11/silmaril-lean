module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithLetCase.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithLetCase.Native
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithLetCase.Soundness

/-! # Typed region let₁-case by postcomposition -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithLetCase

open Paper.RetainedLet (returnOnce)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem distributed_typed {Γ : VCtx τ} {L : LCtx τ} {A B D : τ} {e a b : Tm Φ} {k : Region Φ}
    (he : Tm.HasType Γ e (coprod A B)) (ha : Tm.HasType (A :: Γ) a D)
    (hb : Tm.HasType (B :: Γ) b D) (hk : HasType (D :: Γ) k L) :
    HasType Γ (distributed e a b k) L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithLetCase.distributed_typed he ha hb hk

theorem distributed_valueBranches {Γ : VCtx τ} {L : LCtx τ}
    {A B D : τ} {e a b : Tm Φ} {k : Region Φ}
    (he : Tm.HasType Γ e (coprod A B)) (ha : Tm.HasType (A :: Γ) a D)
    (hb : Tm.HasType (B :: Γ) b D) (hk : ValueBranches (D :: Γ) k L) :
    ValueBranches Γ (distributed e a b k) L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithLetCase.distributed_valueBranches he ha hb hk

/-- Any contextual extension proving the exact singleton-return equation
also proves the printed equation for an arbitrary typed continuation. -/
theorem of_return {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    {Γ : VCtx τ} {L : LCtx τ} {A B D : τ} {e a b : Tm Φ} {k : Region Φ}
    (he : Tm.HasType Γ e (coprod A B)) (ha : Tm.HasType (A :: Γ) a D)
    (hb : Tm.HasType (B :: Γ) b D) (hk : HasType (D :: Γ) k L)
    (h : Paper.Extension.Eqv Seed Γ (returnOnce (.case e a b))
      (.case e (returnOnce a) (returnOnce b)) [D]) :
    Paper.Extension.Eqv Seed Γ (.let₁ (.case e a b) k) (distributed e a b k) L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithLetCase.of_return he ha hb hk h

/-- The printed two-arm region equation at its original typed interface.
[Companion declaration](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Region/Eqv.lean#L984-L994). -/
theorem distribute {Γ : VCtx τ} {L : LCtx τ} {A B D : τ} {e a b : Tm Φ} {k : Region Φ}
    (he : Tm.HasType Γ e (coprod A B)) (ha : Tm.HasType (A :: Γ) a D)
    (hb : Tm.HasType (B :: Γ) b D) (hk : HasType (D :: Γ) k L) :
    Eqv Γ (.let₁ (.case e a b) k) (distributed e a b k) L :=
  let step := Step.split he ha hb
  of_return he ha hb hk (.extra step.valueBranches.1.hasType step.valueBranches.2.hasType step)

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V)
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The common chosen arrow is given by the existing exact return-fusion law. -/
theorem step_denotes : Paper.Extension.Singleton.SeedDenotes (Seed := Step (Φ := Φ)) J M :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithLetCase.step_denotes J M

variable (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
    Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)

include shared in
theorem Eqv.sound {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Paper.Extension.Eqv.sound J M shared (step_denotes (Φ := Φ) J M) h hr hs

include shared in
theorem denote_distribute {Γ : VCtx τ} {L : LCtx τ} {A B D : τ}
    {e a b : Tm Φ} {k : Region Φ} (he : Tm.HasType Γ e (coprod A B))
    (ha : Tm.HasType (A :: Γ) a D) (hb : Tm.HasType (B :: Γ) b D)
    (hk : HasType (D :: Γ) k L) :
    denoteRegion J M (.let₁ (.case he ha hb) hk) =
      denoteRegion J M (distributed_typed he ha hb hk) :=
  (distribute he ha hb hk).sound J M shared _ _

/-- Descend the existing coherent categorical interpretation to this opt-in quotient. -/
@[expose] noncomputable def denoteFunctor :
    Paper.Extension.Singleton.TypeCategory (Step (τ := τ) (Φ := Φ)) ⥤ C :=
  Paper.Extension.Singleton.denoteFunctor J M shared (step_denotes (Φ := Φ) J M)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithLetCase
