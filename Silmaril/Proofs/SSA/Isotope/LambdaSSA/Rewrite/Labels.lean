module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # Typed injections for local and outward CFG edges -/

public section

universe v u w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

theorem ofFnAt {τ : Type w} {n : Nat} (R : Fin n → τ) (i : Fin n) :
    At (List.ofFn R) i (R i) := by
  simp [At, i.isLt]

theorem localAt {τ : Type w} {n : Nat} (R : Fin n → τ) (i : Fin n) (L : LCtx τ) :
    At (List.ofFn R ++ L) i (R i) := by
  simp [At, List.getElem?_append_left, i.isLt]

theorem exitAt {τ : Type w} {n : Nat} (R : Fin n → τ) {L : LCtx τ}
    {ℓ : Nat} {A : τ} (h : At L ℓ A) :
    At (List.ofFn R ++ L) (n + ℓ) A := by
  simpa [At, List.getElem?_append_right] using h

variable {V : Type u} [Category.{v} V] [CartesianMonoidalCategory V]
  [HasFiniteCoproducts V] {τ : Type w} [TypeFormers τ] (M : TypeModel τ V)

private theorem cast_labelInject {L : LCtx τ} {ℓ : Nat} {A B : τ} (h : A = B)
    (ha : At L ℓ A) (hb : At L ℓ B) :
    eqToHom (congrArg M.obj h) ≫ labelInject M ℓ hb = labelInject M ℓ ha := by
  subst B
  simp

set_option backward.isDefEq.respectTransparency false in
theorem labelAppendSplit_local {n : Nat} (R : Fin n → τ) (i : Fin n) (L : LCtx τ) :
    labelInject M i (localAt R i L) ≫ labelAppendSplit M (List.ofFn R) L =
      labelInject M i (ofFnAt R i) ≫ coprod.inr := by
  conv => lhs; arg 1; unfold labelInject
  rw [labelAppendSplit, Category.assoc, Sigma.ι_comp_desc]
  unfold labelAppendRoute
  rw [dite_eq_left (by simp)]
  rw [← Category.assoc, cast_labelInject]
  exact (List.getElem?_eq_some_iff.mp (localAt R i L)).2.symm

set_option backward.isDefEq.respectTransparency false in
theorem labelAppendSplit_exit {n : Nat} (R : Fin n → τ) {L : LCtx τ}
    {ℓ : Nat} {A : τ} (h : At L ℓ A) :
    labelInject M (n + ℓ) (exitAt R h) ≫ labelAppendSplit M (List.ofFn R) L =
      labelInject M ℓ h ≫ coprod.inl := by
  conv => lhs; arg 1; unfold labelInject
  rw [labelAppendSplit, Category.assoc, Sigma.ι_comp_desc]
  unfold labelAppendRoute
  rw [dite_eq_right (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [← Category.assoc, cast_labelInject]
  exact (List.getElem?_eq_some_iff.mp (exitAt R h)).2.symm

set_option backward.isDefEq.respectTransparency false in
theorem labelObjToFinite_local {n : Nat} (R : Fin n → τ) (i : Fin n)
    (h : At (List.ofFn R) i (R i)) :
    labelInject M i h ≫ labelObjToFinite M R = finiteLabelInject M R i := by
  unfold labelInject labelObjToFinite
  rw [Category.assoc, Sigma.ι_comp_desc]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
