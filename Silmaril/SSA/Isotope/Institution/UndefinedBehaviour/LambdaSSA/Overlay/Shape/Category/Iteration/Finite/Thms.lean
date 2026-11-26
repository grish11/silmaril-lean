module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Semantics
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Refinement

/-! # Exact classification and refinement of certified finite overlay loops -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {X A B : Ty κ}
variable {M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ))}
variable {captures points results states : Nat}
variable (C : Carrier M X A B captures points results states)

/-- The executable classification gives the whole shaped observation.
A scan that finds no terminal row denotes ordinary divergence. -/
theorem classify (r : Region Φ [A, X] [.coprod B A]) (table : Table captures points results states)
    (certificate : Certified C r table) (c : Fin captures) (p : Fin points) :
    (iterateCaptured M r).run 0 (pairPayload (C.capture c) (C.invocation p).1) (C.invocation p).2 =
      (execute (table c) p).behaviour C :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.classify C r table certificate c p

/-- At every coded start the check decides the existing pointwise shaped
refinement order, with more permissive behaviours on the right. -/
theorem check_iff (lower upper : Table captures points results states)
    {r t : Region Φ [A, X] [.coprod B A]}
    (hr : Certified C r lower) (ht : Certified C t upper) :
    check lower upper = true ↔ ∀ c p,
      (iterateCaptured M r).run 0 (pairPayload (C.capture c) (C.invocation p).1) (C.invocation p).2 ≤
      (iterateCaptured M t).run 0 (pairPayload (C.capture c) (C.invocation p).1) (C.invocation p).2 :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.check_iff C lower upper hr ht

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
