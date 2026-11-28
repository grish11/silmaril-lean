module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.ExactSum.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.ExactSum

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (return_bind)
open CategoryTheory

universe v w x

variable {α : Type w} {σ : Type x} {κ : Type v} {atomType : α → κ → Prop}
  {A B : Ty κ} {Z : Interface α σ atomType}

private theorem inl_comp_run (f : single (.coprod A B) ⟶ Z)
    (a : (single (σ := σ) (atomType := atomType) A).Payload 0) (s : σ) :
    (sumInl A B ≫ f).run 0 a s = f.run 0 ⟨.inl a.val, .inl a.property⟩ s := by
  rw [comp_run]
  exact (return_bind 0 (.inl a.val) s f.total).trans
    (f.total_typed 0 ⟨.inl a.val, .inl a.property⟩ s)

private theorem inr_comp_run (f : single (.coprod A B) ⟶ Z)
    (b : (single (σ := σ) (atomType := atomType) B).Payload 0) (s : σ) :
    (sumInr A B ≫ f).run 0 b s = f.run 0 ⟨.inr b.val, .inr b.property⟩ s := by
  rw [comp_run]
  exact (return_bind 0 (.inr b.val) s f.total).trans
    (f.total_typed 0 ⟨.inr b.val, .inr b.property⟩ s)

theorem sumInl_desc (f : single A ⟶ Z) (g : single B ⟶ Z) : sumInl A B ≫ sumDesc f g = f := by
  apply arrow_ext
  intro i a s
  have hi := Fin.eq_zero i
  subst i
  exact (inl_comp_run (sumDesc f g) a s).trans rfl

theorem sumInr_desc (f : single A ⟶ Z) (g : single B ⟶ Z) : sumInr A B ≫ sumDesc f g = g := by
  apply arrow_ext
  intro i b s
  have hi := Fin.eq_zero i
  subst i
  exact (inr_comp_run (sumDesc f g) b s).trans rfl

theorem sum_hom_ext {f g : single (.coprod A B) ⟶ Z}
    (hl : sumInl A B ≫ f = sumInl A B ≫ g) (hr : sumInr A B ≫ f = sumInr A B ≫ g) : f = g := by
  apply arrow_ext
  intro i a s
  have hi := Fin.eq_zero i
  subst i
  obtain ⟨v, typed⟩ := a
  cases typed with
  | inl h =>
    exact (inl_comp_run f ⟨_, h⟩ s).symm.trans
      ((congrArg (fun k : single A ⟶ Z => k.run 0 ⟨_, h⟩ s) hl).trans (inl_comp_run g ⟨_, h⟩ s))
  | inr h =>
    exact (inr_comp_run f ⟨_, h⟩ s).symm.trans
      ((congrArg (fun k : single B ⟶ Z => k.run 0 ⟨_, h⟩ s) hr).trans (inr_comp_run g ⟨_, h⟩ s))

theorem empty_hom_ext (f g : single .empty ⟶ Z) : f = g :=
  arrow_ext fun _ a _ => (noEmptyPayload (payloadAtZero a)).elim

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.ExactSum
