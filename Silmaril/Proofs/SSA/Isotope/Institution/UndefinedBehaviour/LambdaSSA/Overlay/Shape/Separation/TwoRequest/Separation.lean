module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Soundness

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest

open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration

private def tests (p q : Endpoint) : Prop :=
  ∀ first next root step,
    let h := prefixHandler first next root step
    (p.execute h 0).refines (q.execute h 0)

private theorem root_row {p q : Endpoint}
    (all : tests p q) :
    p.first = q.first := by
  by_contra different
  let h := prefixHandler p.first p.first (.fault 1) .diverge
  have left : h p.first 0 = .fault 1 := by simp [h, prefixHandler]
  have right : h q.first 0 = .diverge := by simp [h, prefixHandler, Ne.symm different]
  have order : (p.execute h 0).refines (q.execute h 0) := all p.first p.first (.fault 1) .diverge
  simp [Endpoint.execute, left, right, Result.refines] at order

private theorem second_row {p q : Endpoint}
    (all : tests p q)
    (first : p.first = q.first) (i : Tag) :
    (p.next i).key = (q.next i).key := by
  by_contra different
  let h := prefixHandler p.first (p.next i).key (.reply i 1) (.fault 2)
  have leftRoot : h p.first 0 = .reply i 1 := by simp [h, prefixHandler]
  have rightRoot := first ▸ leftRoot
  have leftNext : h (p.next i).key 1 = .fault 2 := by simp [h, prefixHandler]
  have rightNext : h (q.next i).key 1 = .diverge := by simp [h, prefixHandler, Ne.symm different]
  have order : (p.execute h 0).refines (q.execute h 0) :=
    all p.first (p.next i).key (.reply i 1) (.fault 2)
  simp [Endpoint.execute, Row.execute, leftRoot, rightRoot, leftNext, rightNext, Result.refines] at order

theorem normal_of_prefixes {p q : Endpoint}
    (all : ∀ first next root step,
      let h := prefixHandler first next root step
      denote p.region h.model 0 ≤ denote q.region h.model 0) :
    NormalRefines p q := by
  have run : tests p q := fun first next root step => by
    apply (result_order _ _).mp
    simpa only [finite_observe] using all first next root step
  have first := root_row run
  refine ⟨first, fun i => ⟨second_row run first i, fun j => ?_⟩⟩
  have next := second_row run first i
  let h := prefixHandler p.first (p.next i).key (.reply i 1) (.reply j 2)
  have leftRoot : h p.first 0 = .reply i 1 := by simp [h, prefixHandler]
  have rightRoot := first ▸ leftRoot
  have leftNext : h (p.next i).key 1 = .reply j 2 := by simp [h, prefixHandler]
  have rightNext := next ▸ leftNext
  have order : (p.execute h 0).refines (q.execute h 0) :=
    run p.first (p.next i).key (.reply i 1) (.reply j 2)
  simp only [Endpoint.execute, Row.execute, leftRoot, rightRoot, leftNext, rightNext] at order
  generalize (p.next i).exit j = a at order ⊢
  generalize (q.next i).exit j = b at order ⊢
  cases a <;> cases b <;> simp_all [Exit.Refines, Exit.result, Result.refines]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest
