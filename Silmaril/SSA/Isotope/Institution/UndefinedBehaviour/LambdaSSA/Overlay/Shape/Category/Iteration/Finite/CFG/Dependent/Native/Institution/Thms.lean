module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Institution.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Normalize.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Institution.Soundness

/-! # Native finite comparison in the stateful observational institution -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

open CategoryTheory (Discrete)
open Institution.Observational (lambdaSSA)
open Syntax (Primitives emptyBindings Bindings.push model)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {X : Syntax.Ty} {R L : List Syntax.Ty}
variable {captures seeds results states : Nat}

/-- The comparison succeeds exactly when there is no supported counterexample. -/
theorem counterexample_eq_none_iff (left right : Readback Φ X R L)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states) :
    counterexample left right C prim = none ↔ check left right C prim = true :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.Institution.counterexample_eq_none_iff left right C prim

/-- Every failed check exposes a capture and initial state. -/
theorem counterexample_of_check_false (left right : Readback Φ X R L)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states)
    (failed : check left right C prim = false) :
    ∃ c s, counterexample left right C prim = some (c, s) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.Institution.counterexample_of_check_false
    left right C prim failed

variable [DecidableEq Φ] {raw target : Typed Φ [X] L} {left right : Readback Φ X R L}

/-- At each coded capture, the comparison decides satisfaction of the
installed observational refinement sentence on the original typed CFGs.
Each model uses the supplied deterministic primitive interpreter. -/
theorem check_satisfies_iff (hl : recognizeRouterUnits R raw = some left)
    (hr : recognizeRouterUnits R target = some right)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states) :
    check left right C prim = true ↔ ∀ c : Fin captures,
      let M := model prim (emptyBindings.push (C.capture c))
      ((lambdaSSA Φ L.length).room [X].length).Sat (Discrete.mk M.raw)
        (.le ⟨raw.val, raw.property.scoped⟩ ⟨target.val, target.property.scoped⟩) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.Institution.check_satisfies_iff hl hr C prim

/-- A reported start violates the lifted shaped order at that captured
packet and initial machine state. -/
theorem counterexample_point (hl : recognizeRouterUnits R raw = some left)
    (hr : recognizeRouterUnits R target = some right)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states)
    {c : Fin captures} {s : Fin states}
    (found : counterexample left right C prim = some (c, s)) :
    let M := model prim (emptyBindings.push (C.capture c))
    ¬ Shape.denote (.native raw) M s ≤ Shape.denote (.native target) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.Institution.counterexample_point hl hr C prim found

/-- One supported witness refutes observational validity over all models
at the same value and state universes as the checked interpreter. -/
theorem counterexample_refutes (hl : recognizeRouterUnits R raw = some left)
    (hr : recognizeRouterUnits R target = some right)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states)
    {c : Fin captures} {s : Fin states}
    (found : counterexample left right C prim = some (c, s)) :
    ¬ UB.Refines.{u,0,0,0} raw target := by
  intro allModels
  exact counterexample_point hl hr C prim found
    ((native_refines_iff raw target).mpr allModels (model prim (emptyBindings.push (C.capture c))).raw s)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
