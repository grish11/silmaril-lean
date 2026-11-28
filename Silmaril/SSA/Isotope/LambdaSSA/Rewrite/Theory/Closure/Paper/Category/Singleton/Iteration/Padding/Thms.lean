module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Padding.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Classes.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonPadding

/-! # Unreachable padding in default Paper

The simulation statements are separate from the bookkeeping of a
particular state sum. `iterate_padStep` and `padStep_square` hold for any
padding `U`, class map `u` and section `s`. The `short` lemmas supply
those for one layout: the interleaved pairs with the first `A` duplicate
missing.
-/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem sumInl_sumDesc {U X T : τ} (a : ofType (Φ := Φ) U ⟶ ofType T) (b : ofType (Φ := Φ) X ⟶ ofType T) :
    sumInl U X ≫ sumDesc a b = a :=
  SingletonPadding.inl_desc a b

theorem sumInr_sumDesc {U X T : τ} (a : ofType (Φ := Φ) U ⟶ ofType T) (b : ofType (Φ := Φ) X ⟶ ofType T) :
    sumInr U X ≫ sumDesc a b = b :=
  SingletonPadding.inr_desc a b

/-- A copair followed by a map is the copair of the composites. -/
theorem sumDesc_comp {U X T W : τ} (a : ofType (Φ := Φ) U ⟶ ofType T) (b : ofType (Φ := Φ) X ⟶ ofType T)
    (f : ofType (Φ := Φ) T ⟶ ofType W) : sumDesc a b ≫ f = sumDesc (a ≫ f) (b ≫ f) :=
  SingletonPadding.desc_comp a b f

/-- A map out of an exact sum is the copair of its restrictions. -/
theorem sumDesc_eta {U X T : τ} (x : ofType (Φ := Φ) (Silmaril.coprod U X) ⟶ ofType T) :
    sumDesc (sumInl U X ≫ x) (sumInr U X ≫ x) = x :=
  (SingletonPadding.desc_eta x).symm

theorem sumDesc_inl_inr (U X : τ) : sumDesc (sumInl (Φ := Φ) U X) (sumInr U X) = 𝟙 _ :=
  SingletonPadding.desc_inl_inr U X

variable (U : τ) {X Z Y : τ} (u : ofType (Φ := Φ) U ⟶ ofType Z) (s : ofType (Φ := Φ) Z ⟶ ofType X)
  (J : ofType (Φ := Φ) X ⟶ ofType Y ⨿ ofType X) (T : ofType (Φ := Φ) Z ⟶ ofType Y ⨿ ofType Z)

/-- Unreachable padding does not change the loop: entering the padded
table at an old state is the original loop. There is no premise. The
embedding of the old states is a constructor injection, and guarded
iteration is uniform along it. -/
theorem iterate_padStep : iterate J = sumInr U X ≫ iterate (padStep U u s J T) :=
  SingletonPadding.iterate_padStep U u s J T

/-- If `h` is a simulation of `J` onto `T` and `s` is a section of `h`,
then `[u, h]` is a simulation of the padded table onto `T`. -/
theorem padStep_square (h : ofType (Φ := Φ) X ⟶ ofType Z) (sect : s ≫ h = 𝟙 _)
    (square : J ≫ coprod.map (𝟙 _) h = h ≫ T) :
    padStep U u s J T ≫ coprod.map (𝟙 _) (sumDesc u h) = sumDesc u h ≫ T :=
  SingletonPadding.padStep_square U u s J T h sect square

variable (A B : τ)

/-- The pairs' fold is the class of the first `A` duplicate and the short fold. -/
theorem pairFold_split (n : Nat) :
    pairFold (Φ := Φ) A B (n + 1) = sumDesc (sumInl A B) (shortFold A B n) :=
  SingletonPadding.short_split A B n

/-- Each class has a state among the short states. -/
theorem shortSection_fold (n : Nat) : shortSection (Φ := Φ) A B n ≫ shortFold A B n = 𝟙 _ :=
  SingletonPadding.shortSection_fold A B n

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
