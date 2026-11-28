module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Soundness.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Extension

/-! # Exact typing and model soundness for contextual extensions -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

/-- Each derivation retains both exact typing interfaces. -/
theorem Eqv.typed (h : Eqv Seed Γ r s L) : HasType Γ r L ∧ HasType Γ s L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Extension.typed h

/-- Replace each seed instance by an instance in a larger contextual relation. -/
theorem Eqv.mapSeed {Target : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (h : Eqv Seed Γ r s L) (incl : ∀ {Γ r s L}, Seed Γ r s L → Target Γ r s L) :
    Eqv Target Γ r s L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Extension.mapSeed incl h

theorem Eqv.refl (hr : HasType Γ r L) : Eqv Seed Γ r r L :=
  .paper (.refl hr)

/-- Interpret a contextual extension in standard Paper when its seeds
already have standard Paper proofs. -/
theorem Eqv.toPaper (sound : ∀ {Γ L r s}, Seed Γ r s L → Paper.Eqv Γ r s L)
    (h : Eqv Seed Γ r s L) : Paper.Eqv Γ r s L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Extension.toPaper sound h

/-- Rename captured variables using constructor-valued substitution. -/
theorem Eqv.renameVars {Δ : VCtx τ} {ρ : Nat → Nat}
    (h : Eqv Seed Γ r s L) (hρ : Ren Γ Δ ρ) : Eqv Seed Δ (r.renameVars ρ) (s.renameVars ρ) L := by
  simpa only [renameVars_eq_substVars] using h.substVars (θ := Tm.var ∘ ρ)
    (fun _ _ hi => Tm.BranchValue.var (hρ hi))

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- Sound extra equations and the Paper model assumptions give one structural
arrow for both endpoints of every contextual derivation. -/
theorem Eqv.denotes
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    (seedDenotes : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Seed Γ r s L →
      ∀ (hr : HasType Γ r L) (hs : HasType Γ s L),
        ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f)
    (h : Eqv Seed Γ r s L) :
    ∃ f, RegionDenotes J M h.typed.1 f ∧ RegionDenotes J M h.typed.2 f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Extension.denotes J M shared seedDenotes h

/-- Contextual derivations preserve the chosen denotation. -/
theorem Eqv.sound
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    (seedDenotes : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Seed Γ r s L →
      ∀ (hr : HasType Γ r L) (hs : HasType Γ s L),
        ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f)
    (h : Eqv Seed Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  obtain ⟨_, dr, ds⟩ := h.denotes J M shared seedDenotes
  exact (RegionDenotes.eq_denote (h := hr) J M dr).symm.trans (RegionDenotes.eq_denote (h := hs) J M ds)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension
