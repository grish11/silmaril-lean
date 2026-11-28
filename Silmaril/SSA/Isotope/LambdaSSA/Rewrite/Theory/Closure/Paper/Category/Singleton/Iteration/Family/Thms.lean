module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Family.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonFamily

/-! # Laws of finite family sums and of the fold along a tag map

All of these are equations of default Paper.
-/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {m N : Nat}

theorem famInj_famDesc {T : τ} (A : Fin (m + 1) → τ) (x : ∀ i, ofType (Φ := Φ) (A i) ⟶ ofType T)
    (i : Fin (m + 1)) : famInj m A i ≫ famDesc m A x = x i :=
  SingletonFamily.inj_desc m A x i

theorem famDesc_comp {T W : τ} (A : Fin (m + 1) → τ) (x : ∀ i, ofType (Φ := Φ) (A i) ⟶ ofType T)
    (f : ofType (Φ := Φ) T ⟶ ofType W) : famDesc m A x ≫ f = famDesc m A fun i => x i ≫ f :=
  SingletonFamily.desc_comp m A x f

theorem famDesc_famInj (A : Fin (m + 1) → τ) : famDesc m A (famInj (Φ := Φ) m A) = 𝟙 _ :=
  SingletonFamily.desc_inj m A

/-- Every summand of a family with at least two summands splits the sum:
case analysis on the other summands and on summand `i` is an iso. -/
theorem famSplit (A : Fin (m + 2) → τ) (i : Fin (m + 2)) :
    IsIso (sumDesc (famMiss (Φ := Φ) m A i) (famInj (m + 1) A i)) :=
  SingletonFamily.split m A i

/-- The class-map equation: source state `k` is sent to its class. -/
theorem famInj_tagFold (A : Fin (m + 1) → τ) (f : Fin (N + 1) → Fin (m + 1)) (k : Fin (N + 1)) :
    famInj (Φ := Φ) N (fun k => A (f k)) k ≫ tagFold A f = famInj m A (f k) :=
  SingletonFamily.inj_tagFold A f k

/-- A right inverse of the tag map gives a section of the class map. -/
theorem tagSection_fold (A : Fin (m + 1) → τ) (f : Fin (N + 1) → Fin (m + 1))
    (g : Fin (m + 1) → Fin (N + 1)) (hg : ∀ c, f (g c) = c) :
    tagSection (Φ := Φ) A f g hg ≫ tagFold A f = 𝟙 _ :=
  SingletonFamily.tagSection_fold A f g hg

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
