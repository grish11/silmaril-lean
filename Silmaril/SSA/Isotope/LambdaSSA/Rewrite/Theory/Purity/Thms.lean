module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Purity
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Purity
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.PureCfg

/-! # Denotation of all typed λSSA pure expressions -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

namespace Silmaril.Isotope.LambdaSSA

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {τ : Type u₃} [TypeFormers τ] {Φ : Type u₄} [HasTy Φ τ]
  {ε : Type u₅} [HasEff Φ ε] {pureEff : ε}

section Expressions

variable (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- A typed pure expression is interpreted by a value arrow whenever
primitive instructions with the pure effect have value interpretations. -/
theorem Tm.Pure.denotes_map {Γ : VCtx τ} {a : Tm Φ} {A : τ}
    (hp : Pure pureEff a) (ht : HasType Γ a A)
    (hInstr : ∀ f : Φ, IsPure pureEff f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p) :
    ∃ p : ctxObj M Γ ⟶ M.obj A, Denotes J M ht (J.map p) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.pure_denotes_map J M hInstr ht hp

end Expressions

section Cfg

variable [Iteration C] [ElgotCategory C]

/-- Figure 20's outward-entry β rule for every native typed pure argument. -/
theorem Region.cfgBrExit_sound_of_pure (J : V ⥤ C) [StrongElgotFreydCategory J]
    (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
    (hInstr : ∀ f : Φ, IsPure pureEff f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {ℓ : Nat} {a : Tm Φ} {A : τ} {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (hℓ : At L ℓ A) (ha : Tm.HasType Γ a A) (hp : Tm.Pure pureEff a)
    (hb : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
    (hs : HasType Γ (.cfg (.br (n + 1 + ℓ) a) (n + 1) blocks) L) :
    denoteRegion J M hs = denoteRegion J M (.br hℓ ha) := by
  obtain ⟨_, _, _, ds, dt⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfgBrExit_pure_common J M hInstr R hℓ ha hp hb
  exact (RegionDenotes.eq_denote (h := hs) J M ds).symm.trans (RegionDenotes.eq_denote J M dt)

/-- Figure 20's local-entry β rule for every native typed pure argument. -/
theorem Region.cfgBrLocal_sound_of_pure (J : V ⥤ C) [StrongElgotFreydCategory J]
    (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
    (hInstr : ∀ f : Φ, IsPure pureEff f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (i : Fin (n + 1)) (ha : Tm.HasType Γ a (R i)) (hp : Tm.Pure pureEff a)
    (hb : ∀ j, HasType (R j :: Γ) (blocks j) (List.ofFn R ++ L))
    (hs : HasType Γ (.cfg (.br i a) (n + 1) blocks) L) :
    denoteRegion J M hs = denoteRegion J M (.cfg R (.let₁ ha (hb i)) hb) := by
  obtain ⟨_, _, _, ds, dt⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfgBrLocal_pure_common J M hInstr R i ha hp hb
  exact (RegionDenotes.eq_denote (h := hs) J M ds).symm.trans (RegionDenotes.eq_denote J M dt)

end Cfg

end Silmaril.Isotope.LambdaSSA
