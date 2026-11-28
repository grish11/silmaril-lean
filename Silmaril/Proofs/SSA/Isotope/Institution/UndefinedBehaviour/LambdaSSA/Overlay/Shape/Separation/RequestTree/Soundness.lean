module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.RequestTree.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest
  (Instr Exits Handler Tag exit_denote exit_order request_bind_finite resultBehaviour)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax (Bindings model)

universe v w

theorem sound (p q : Tree) (h : p.Refines q) {Γ : List (Silmaril.Ty Empty)}
    (M : Institution.Observational.Model.{0,v,w} Instr Γ.length) (s : M.σ) :
    denote (p.region (Γ := Γ)) M s ≤ denote (q.region (Γ := Γ)) M s := by
  induction p generalizing q Γ with
  | stop e =>
    cases q with
    | stop e' =>
      change denote (e.region (Γ := Γ)) M s ≤ denote (e'.region (Γ := Γ)) M s
      rw [exit_denote, exit_denote]
      exact (exit_order e e' s).mpr h
    | ask => exact False.elim h
  | ask f l r left right =>
    cases q with
    | stop e =>
      cases e with
      | ret => exact False.elim h
      | ub => exact le_top
    | ask g l' r' =>
      obtain ⟨rfl, hl, hr⟩ := h
      refine Behaviour.bind_mono le_rfl ?_
      intro i a t
      by_cases tag : i = (0 : Tag)
      · simpa only [ite_eq_left tag] using left l' hl (Γ := Exits.get i :: Γ) (extendModel M a) t
      · simpa only [ite_eq_right tag] using right r' hr (Γ := Exits.get i :: Γ) (extendModel M a) t

theorem finite_observe {Γ : List (Silmaril.Ty Empty)} {n : Nat} (p : Tree) (h : Handler n)
    (env : Bindings Γ) (s : Fin n) :
    Shape.denote p.region (model h.primitives env) s = resultBehaviour (p.execute h s) := by
  induction p generalizing Γ s with
  | stop e =>
    change denote (e.region (Γ := Γ)) (model h.primitives env).raw s = resultBehaviour (e.result s)
    rw [exit_denote]
    cases e <;> rfl
  | ask f l r left right =>
    rw [Tree.region, request_bind_finite, Tree.execute]
    cases h f s with
    | fault | diverge => rfl
    | reply i t =>
      by_cases tag : i = (0 : Tag)
      · simpa only [ite_eq_left tag] using left _ t
      · simpa only [ite_eq_right tag] using right _ t

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree
