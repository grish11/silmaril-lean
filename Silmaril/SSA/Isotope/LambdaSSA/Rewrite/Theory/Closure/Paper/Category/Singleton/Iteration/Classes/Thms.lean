module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Classes.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonClasses

/-! # Two duplicated classes are phases of their pair -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Default Paper is uniform along each of its isos. This is rolling. -/
theorem iterate_uniformity_iso {X W Y : TypeCategory (τ := τ) Φ} (ψ : X ≅ W) (J : X ⟶ Y ⨿ X) :
    iterate J = ψ.hom ≫ iterate (ψ.inv ≫ J ≫ coprod.map (𝟙 Y) ψ.hom) :=
  SingletonClasses.iterate_iso ψ J

variable (A B : τ)

/-- Under the reassociation, the fold of the pair's phases is the sum of
the two class folds. -/
theorem pairIso_fold (n : Nat) :
    (pairIso (Φ := Φ) A B n).hom ≫ phaseFold (Silmaril.coprod A B) n = pairFold A B n :=
  SingletonClasses.pairIso_fold A B n

/-- The first `A` duplicate folds to `A`. -/
theorem pairFold_inl (n : Nat) :
    sumInl A (Silmaril.coprod B (pairPhases A B n)) ≫ pairFold (Φ := Φ) A B (n + 1) = sumInl A B :=
  SingletonClasses.pairFold_inl A B n

/-- The first `B` duplicate folds to `B`. -/
theorem pairFold_inr_inl (n : Nat) :
    sumInl B (pairPhases A B n) ≫ sumInr A (Silmaril.coprod B (pairPhases A B n)) ≫
      pairFold (Φ := Φ) A B (n + 1) = sumInr A B :=
  SingletonClasses.pairFold_inr_inl A B n

/-- The later duplicates fold as before. -/
theorem pairFold_inr_inr (n : Nat) :
    sumInr B (pairPhases A B n) ≫ sumInr A (Silmaril.coprod B (pairPhases A B n)) ≫
      pairFold (Φ := Φ) A B (n + 1) = pairFold A B n :=
  SingletonClasses.pairFold_inr_inr A B n

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
