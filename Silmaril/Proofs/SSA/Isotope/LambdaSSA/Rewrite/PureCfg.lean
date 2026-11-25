module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Defs
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Purity
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Purity
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Soundness

/-! # CFG entry β for the native pure expression judgment -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  {ε : Type u₅} [HasEff Φ ε] {pureEff : ε}

theorem cfgBrExit_pure_common
    (hInstr : ∀ f : Φ, IsPure pureEff f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {ℓ : Nat} {a : Tm Φ} {A : τ} {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (hℓ : At L ℓ A) (ha : Tm.HasType Γ a A) (hp : Tm.Pure pureEff a)
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    ∃ (hs : Region.HasType Γ (.cfg (.br (n + 1 + ℓ) a) (n + 1) blocks) L)
      (ht : Region.HasType Γ (.br ℓ a) L), ∃ f, RegionDenotes J M hs f ∧ RegionDenotes J M ht f := by
  obtain ⟨p, dp⟩ := pure_denotes_map J M hInstr ha hp
  exact cfgBrExit_map_common J M R hℓ ha p dp hb

theorem cfgBrLocal_pure_common
    (hInstr : ∀ f : Φ, IsPure pureEff f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (i : Fin (n + 1)) (ha : Tm.HasType Γ a (R i)) (hp : Tm.Pure pureEff a)
    (hb : ∀ j, Region.HasType (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    ∃ (hs : Region.HasType Γ (.cfg (.br i a) (n + 1) blocks) L)
      (ht : Region.HasType Γ (.cfg (.let₁ a (blocks i)) (n + 1) blocks) L),
      ∃ f, RegionDenotes J M hs f ∧ RegionDenotes J M ht f := by
  obtain ⟨p, dp⟩ := pure_denotes_map J M hInstr ha hp
  exact cfgBrLocal_map_common J M R i ha p dp hb

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
