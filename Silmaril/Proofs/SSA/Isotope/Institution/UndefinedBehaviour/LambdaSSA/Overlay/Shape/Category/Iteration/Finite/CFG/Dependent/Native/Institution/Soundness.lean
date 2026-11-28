module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Institution.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Normalize.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Refinement

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.Institution

open CategoryTheory (Discrete)
open Silmaril.Isotope
open Silmaril.Isotope.Institution.Observational (lambdaSSA)
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
  (Primitives emptyBindings Bindings.push model)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Codes)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration (routed_order)

universe u

variable {Φ : Type u} [HasTy Φ (Silmaril.Ty Empty)]
variable {X : Silmaril.Ty Empty} {R L : List (Silmaril.Ty Empty)}
variable {captures seeds results states : Nat}

theorem counterexample_eq_none_iff (left right : Readback Φ X R L)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states) :
    counterexample left right C prim = none ↔ check left right C prim = true := by
  simp [counterexample, check, List.mem_finRange, List.all_eq_true]

theorem counterexample_of_check_false (left right : Readback Φ X R L)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states)
    (failed : check left right C prim = false) :
    ∃ c s, counterexample left right C prim = some (c, s) := by
  cases found : counterexample left right C prim with
  | none =>
    have checked := (counterexample_eq_none_iff left right C prim).mp found
    rw [failed] at checked
    contradiction
  | some point => exact ⟨point.1, point.2, rfl⟩

variable [DecidableEq Φ] {raw target : Typed Φ [X] L} {left right : Readback Φ X R L}

theorem check_satisfies_iff (hl : recognizeRouterUnits R raw = some left)
    (hr : recognizeRouterUnits R target = some right)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states) :
    check left right C prim = true ↔ ∀ c : Fin captures,
      let M := model prim (emptyBindings.push (C.capture c))
      ((lambdaSSA Φ L.length).room [X].length).Sat (Discrete.mk M.raw)
        (.le ⟨raw.val, raw.property.scoped⟩ ⟨target.val, target.property.scoped⟩) := by
  rw [check_recognizedRouterUnits_iff hl hr C prim]
  refine forall_congr' fun c => ?_
  let M := model prim (emptyBindings.push (C.capture c))
  exact (native_observe_subset_iff M.raw raw target).symm

theorem counterexample_point (hl : recognizeRouterUnits R raw = some left)
    (hr : recognizeRouterUnits R target = some right)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states)
    {c : Fin captures} {s : Fin states}
    (found : counterexample left right C prim = some (c, s)) :
    let M := model prim (emptyBindings.push (C.capture c))
    ¬ Shape.denote (.native raw) M s ≤ Shape.denote (.native target) M s := by
  have rejected := List.find?_some found
  have failed : ¬ (left.execute C prim c s).refines (right.execute C prim c s) := by
    simpa using rejected
  dsimp only
  rw [classify_recognizedRouterUnits hl C prim c s, classify_recognizedRouterUnits hr C prim c s]
  exact fun le => failed ((routed_order C.carrier _ _).mp le)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.Institution
