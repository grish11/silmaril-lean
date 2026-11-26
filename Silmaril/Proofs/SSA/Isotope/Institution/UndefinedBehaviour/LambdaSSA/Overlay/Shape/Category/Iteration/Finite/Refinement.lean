module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Semantics

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {X A B : Ty κ}
variable {M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ))}
variable {captures points results states : Nat}
variable (C : Carrier M X A B captures points results states)

private theorem behaviour_order (lower upper : Result results states) :
    lower.behaviour C ≤ upper.behaviour C ↔ lower.refines upper := by
  have resultEq (a b : Fin results) : (C.result a).val = (C.result b).val ↔ a = b :=
    ⟨fun h => C.result.injective (Subtype.ext h), congrArg (fun i => (C.result i).val)⟩
  cases upper <;> cases lower <;>
    simp [Result.behaviour, Result.refines, returnPayload, WithTop.coe_le_coe,
      resultEq]

set_option backward.isDefEq.respectTransparency false in
theorem check_iff (lower upper : Table captures points results states)
    {r t : Region Φ [A, X] [.coprod B A]}
    (hr : Certified C r lower) (ht : Certified C t upper) :
    check lower upper = true ↔ ∀ c p,
      (iterateCaptured M r).run 0 (pairPayload (C.capture c) (C.invocation p).1) (C.invocation p).2 ≤
      (iterateCaptured M t).run 0 (pairPayload (C.capture c) (C.invocation p).1) (C.invocation p).2 := by
  simp only [check, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
  refine forall_congr' fun c => forall_congr' fun p => ?_
  rw [classify C r lower hr, classify C t upper ht]
  exact (behaviour_order C _ _).symm

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
