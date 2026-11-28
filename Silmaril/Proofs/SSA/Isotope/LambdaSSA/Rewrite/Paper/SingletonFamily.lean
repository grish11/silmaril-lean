module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Family.Defs

/-! # Sums of finite families in default Paper -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonFamily

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option backward.isDefEq.respectTransparency false

theorem inj_desc {T : τ} : ∀ (m : Nat) (A : Fin (m + 1) → τ) (x : ∀ i, ofType (Φ := Φ) (A i) ⟶ ofType T)
    (i : Fin (m + 1)), famInj m A i ≫ famDesc m A x = x i
  | 0, A, x, i => by
    refine Fin.cases ?_ (fun j => j.elim0) i
    exact Category.id_comp _
  | m + 1, A, x, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact sumInl_sumDesc _ _
    · exact (Category.assoc _ _ _).trans
        ((congrArg (famInj m (fun i => A i.succ) j ≫ ·) (sumInr_sumDesc _ _)).trans
          (inj_desc m (fun i => A i.succ) (fun i => x i.succ) j))

theorem desc_comp {T W : τ} : ∀ (m : Nat) (A : Fin (m + 1) → τ)
    (x : ∀ i, ofType (Φ := Φ) (A i) ⟶ ofType T) (f : ofType (Φ := Φ) T ⟶ ofType W),
    famDesc m A x ≫ f = famDesc m A fun i => x i ≫ f
  | 0, _, _, _ => rfl
  | m + 1, A, x, f => (sumDesc_comp _ _ f).trans
      (congrArg (sumDesc (x 0 ≫ f)) (desc_comp m (fun i => A i.succ) (fun i => x i.succ) f))

theorem desc_inj : ∀ (m : Nat) (A : Fin (m + 1) → τ), famDesc m A (famInj (Φ := Φ) m A) = 𝟙 _
  | 0, _ => rfl
  | m + 1, A => by
    have tail : famDesc m (fun i => A i.succ) (fun i => famInj (Φ := Φ) (m + 1) A i.succ) =
        sumInr (A 0) (famSum m fun i => A i.succ) := by
      have e := desc_comp m (fun i => A i.succ) (famInj (Φ := Φ) m fun i => A i.succ)
        (sumInr (A 0) (famSum m fun i => A i.succ))
      rw [desc_inj m, Category.id_comp] at e
      exact e.symm
    exact (congrArg (sumDesc (sumInl (A 0) _)) tail).trans (sumDesc_inl_inr _ _)

theorem inj_cast (m : Nat) (A : Fin (m + 1) → τ) {c i : Fin (m + 1)} (e : c = i) :
    eqToHom (congrArg (fun i => ofType (Φ := Φ) (A i)) e) ≫ famInj m A i = famInj m A c := by
  subst e
  exact Category.id_comp _

/-- Every summand of a family with at least two summands splits the sum. -/
theorem split : ∀ (m : Nat) (A : Fin (m + 2) → τ) (i : Fin (m + 2)),
    IsIso (sumDesc (famMiss (Φ := Φ) m A i) (famInj (m + 1) A i))
  | 0, A, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact split_first (A 0) (A (Fin.succ 0))
    · have j0 : j = 0 := Fin.eq_zero j
      subst j0
      exact split_second (A 0) (A (Fin.succ 0))
  | m + 1, A, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact split_first (A 0) _
    · exact split_under (A 0) _ _ (split m (fun k => A k.succ) j)

variable {m N : Nat}

theorem inj_tagFold (A : Fin (m + 1) → τ) (f : Fin (N + 1) → Fin (m + 1)) (k : Fin (N + 1)) :
    famInj (Φ := Φ) N (fun k => A (f k)) k ≫ tagFold A f = famInj m A (f k) :=
  inj_desc N (fun k => A (f k)) (fun k => famInj m A (f k)) k

theorem tagSection_fold (A : Fin (m + 1) → τ) (f : Fin (N + 1) → Fin (m + 1))
    (g : Fin (m + 1) → Fin (N + 1)) (hg : ∀ c, f (g c) = c) :
    tagSection (Φ := Φ) A f g hg ≫ tagFold A f = 𝟙 _ := by
  have each : (fun c => (eqToHom (congrArg (fun i => ofType (Φ := Φ) (A i)) (hg c).symm) ≫
      famInj N (fun k => A (f k)) (g c)) ≫ tagFold A f) = famInj (Φ := Φ) m A := by
    funext c
    rw [Category.assoc, inj_tagFold]
    exact inj_cast m A (hg c).symm
  exact (desc_comp m A _ (tagFold A f)).trans ((congrArg (famDesc m A) each).trans (desc_inj m A))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonFamily
