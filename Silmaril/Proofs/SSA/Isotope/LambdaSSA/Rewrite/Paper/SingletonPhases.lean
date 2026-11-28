module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Phases.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Rounds.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.PhaseIteration

/-! # The phase system of the default Paper category

Every law used here is a law of default Paper: fixpoint, naturality and
codiagonal of guarded iteration, and uniformity along the two constructor
injections `inl` and `inr` of an exact sum.
-/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonPhases

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open Semantics.Categorical (roundsStep PhaseSystem)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] (A : τ)

set_option backward.isDefEq.respectTransparency false

theorem inl_rep (P : τ) : coprod.inl ≫ (sumIso (Φ := Φ) A P).inv =
    ofRegion (r := .br 0 (.inl (.var 0))) (.br rfl (.inl (.var rfl))) :=
  ((Iso.comp_inv_eq _).2 (sumCofan_inl_sumIso_hom A P).symm).trans (sumCofan_inl A P)

theorem inr_rep (P : τ) : coprod.inr ≫ (sumIso (Φ := Φ) A P).inv =
    ofRegion (r := .br 0 (.inr (.var 0))) (.br rfl (.inr (.var rfl))) :=
  ((Iso.comp_inv_eq _).2 (sumCofan_inr_sumIso_hom A P).symm).trans (sumCofan_inr A P)

theorem uniform_inl (P B : τ) (f : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A)
    (g : ofType (Φ := Φ) (Silmaril.coprod A P) ⟶ ofType B ⨿ ofType (Silmaril.coprod A P))
    (comm : f ≫ coprod.map (𝟙 _) (coprod.inl ≫ (sumIso A P).inv) = (coprod.inl ≫ (sumIso A P).inv) ≫ g) :
    iterate f = (coprod.inl ≫ (sumIso A P).inv) ≫ iterate g := by
  rw [inl_rep] at comm ⊢
  exact iterate_uniformity_ofBranchValue (.inl (.var rfl)) f g comm

theorem uniform_inr (P B : τ) (f : ofType (Φ := Φ) P ⟶ ofType B ⨿ ofType P)
    (g : ofType (Φ := Φ) (Silmaril.coprod A P) ⟶ ofType B ⨿ ofType (Silmaril.coprod A P))
    (comm : f ≫ coprod.map (𝟙 _) (coprod.inr ≫ (sumIso A P).inv) = (coprod.inr ≫ (sumIso A P).inv) ≫ g) :
    iterate f = (coprod.inr ≫ (sumIso A P).inv) ≫ iterate g := by
  rw [inr_rep] at comm ⊢
  exact iterate_uniformity_ofBranchValue (.inr (.var rfl)) f g comm

theorem sum_ext (P : τ) {T : Paper.TypeCategory (τ := τ) Φ} {f g : ofType (Silmaril.coprod A P) ⟶ T}
    (hl : (coprod.inl ≫ (sumIso A P).inv) ≫ f = (coprod.inl ≫ (sumIso A P).inv) ≫ g)
    (hr : (coprod.inr ≫ (sumIso A P).inv) ≫ f = (coprod.inr ≫ (sumIso A P).inv) ≫ g) : f = g := by
  rw [← cancel_epi (sumIso A P).inv]
  apply coprod.hom_ext
  · simpa only [Category.assoc] using hl
  · simpa only [Category.assoc] using hr

/-- The phases of `A` in default Paper. -/
@[expose] noncomputable def system : PhaseSystem (Paper.TypeCategory (τ := τ) Φ) where
  iter := iterate
  fixpoint := iterate_fixpoint
  naturality := iterate_naturality
  codiagonal := iterate_codiagonal
  obj k := ofType (phaseType A k)
  inl k := coprod.inl ≫ (sumIso A (phaseType A k)).inv
  inr k := coprod.inr ≫ (sumIso A (phaseType A k)).inv
  desc k _ u v := (sumIso A (phaseType A k)).hom ≫ coprod.desc u v
  inl_desc k _ u v := by
    rw [Category.assoc, Iso.inv_hom_id_assoc, coprod.inl_desc]
  inr_desc k _ u v := by
    rw [Category.assoc, Iso.inv_hom_id_assoc, coprod.inr_desc]
  ext k _ _ _ hl hr := sum_ext A (phaseType A k) hl hr
  uniform_inl k B f g comm := uniform_inl A (phaseType A k) B f g comm
  uniform_inr k B f g comm := uniform_inr A (phaseType A k) B f g comm

theorem fold_eq : ∀ k, (system (Φ := Φ) A).fold k = phaseFold A k
  | 0 => rfl
  | k + 1 => congrArg (fun φ => (sumIso A (phaseType A k)).hom ≫ coprod.desc (𝟙 _) φ) (fold_eq k)

/-- In default Paper the loop on `n + 1` rounds enters a cycle of `n + 1`
phases, and the phase fold is a simulation of that cycle onto one round. -/
theorem exists_cycle {B : τ} (h : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A) (n : Nat) :
    ∃ (start : ofType (Φ := Φ) A ⟶ ofType (phaseType A n))
      (cycle : ofType (Φ := Φ) (phaseType A n) ⟶ ofType B ⨿ ofType (phaseType A n)),
      start ≫ phaseFold A n = 𝟙 _ ∧
      cycle ≫ coprod.map (𝟙 _) (phaseFold A n) = phaseFold A n ≫ h ∧
      iterate (roundsStep h n) = start ≫ iterate cycle := by
  have c := Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.PhaseIteration.exists_cycle
    (system (Φ := Φ) A) h n
  rw [fold_eq] at c
  exact c

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonPhases
