module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Thms
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Continuation
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheoryTyping
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheorySoundness
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Outward

/-! # Typed CFG commuting and categorical soundness

Pure let substitution into an immediate branch derives the outward CFG
commuting equation. Case selection retains the effects of the payload.
-/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Region

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

section Syntax

variable {τ : Type u₃} [TypeFormers τ] {Φ : Type u₄} [HasTy Φ τ]

theorem RewriteEquiv.refl {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : HasType Γ r L) : RewriteEquiv Γ r r L :=
  .entry (.refl hr)

theorem RewriteEquiv.typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : RewriteEquiv Γ r s L) : HasType Γ r L ∧ HasType Γ s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.rewriteEquiv_typed h

/-- A constructor-valued let followed by an outward branch leaves the CFG
after the same binding and branch, regardless of the local block bodies. -/
theorem RewriteEquiv.cfgLetBrExit {Γ : VCtx τ} {L : LCtx τ} {n ℓ : Nat} {a b : Tm Φ}
    {A B : τ} {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (hℓ : At L ℓ B)
    (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue (A :: Γ) b B)
    (hblocks : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    RewriteEquiv Γ
      (.cfg (.let₁ a (.br (n + 1 + ℓ) b)) (n + 1) blocks) (.let₁ a (.br ℓ b)) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfgLetBrExit R hℓ ha hb hblocks

/-- The label substitution counterexample for the entry equations is identified
after adding constructor-valued let substitution. -/
theorem RewriteEquiv.repaired_example :
    let r : Region Φ := .cfg (.br 1 (.var 0)) 1 (fun _ => .br 1 (.var 0))
    let s : Region Φ := .br 0 (.var 0)
    let σ : Nat → Region Φ := fun _ => .let₁ .unit (.br 0 (.var 0))
    RewriteEquiv [(Silmaril.unit : τ)] (r.lsubst σ) (s.lsubst σ) [Silmaril.unit] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.repaired_example

end Syntax

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- The enlarged typed rewrite theory preserves the categorical region arrow. -/
theorem RewriteEquiv.sound [RegionTypingCoherent (Φ := Φ) J M]
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : RewriteEquiv Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  obtain ⟨_, _, _, dr, ds⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.rewriteEquiv_common J M h
  exact (RegionDenotes.eq_denote (h := hr) J M dr).symm.trans
    (RegionDenotes.eq_denote (h := hs) J M ds)

end Silmaril.Isotope.LambdaSSA.Region
