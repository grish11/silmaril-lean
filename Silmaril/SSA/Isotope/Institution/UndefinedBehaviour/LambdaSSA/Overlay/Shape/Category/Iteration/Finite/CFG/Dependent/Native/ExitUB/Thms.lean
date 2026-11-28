module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Normalize.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Soundness

/-! # Finite comparison through the existing overlay continuations -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

open Syntax (Primitives emptyBindings Bindings.push model)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty]
variable {X : Syntax.Ty} {Γ R L : List Syntax.Ty} {captures seeds results states : Nat}
/-- A selected exit exposes literal UB at the reply state. Other positions
forward the exact payload and state. -/
theorem denote_exitContinuation (M : Institution.Observational.Model.{u,v,w} Φ Γ.length)
    (selected : Fin L.length → Bool) (i : Fin L.length) (a : Value M.α) (s : M.σ) :
    Overlay.denote (exitContinuation (Γ := Γ) selected i) (extendModel M a) s =
      if selected i then ⊤ else WithTop.some {Outcome.ret i a s} :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.ExitUB.denote_exitContinuation
    M selected i a s

/-- Forwarding every exit recovers the unadorned native observation at
each shaped model and initial state. -/
theorem denote_noExitUB (raw : Typed Φ Γ L) (M : Shape.Model.{u,0,v,w} Φ Γ) (s : M.raw.σ) :
    Shape.denote (withExitUB raw (fun _ => false)) M s = Shape.denote (.native raw) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.ExitUB.denote_noExitUB
    raw M s

variable [DecidableEq Φ]
variable {raw target : Typed Φ [X] L} {left right : Readback Φ X R L}

/-- Computing the native result and then marking the selected ordered exit
agrees with the installed overlay denotation of the original CFG. -/
theorem classify_exitUB (accepted : recognizeRouterUnits R raw = some left)
    (selected : Fin L.length → Bool) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (s : Fin states) :
    Shape.denote (withExitUB raw selected) (model prim (emptyBindings.push (C.capture c))) s =
      (left.executeExitUB selected C prim c s).routed C.carrier :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.ExitUB.classify_exitUB
    accepted selected C prim c s

/-- The check decides the original CFGs' shaped order at every coded
capture and initial machine state, with fresh top greatest. -/
theorem checkExitUB_iff (hl : recognizeRouterUnits R raw = some left)
    (hr : recognizeRouterUnits R target = some right) (lUB rUB : Fin L.length → Bool)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states) :
    checkExitUB left right lUB rUB C prim = true ↔ ∀ (c : Fin captures) (s : Fin states),
      let M := model prim (emptyBindings.push (C.capture c))
      Shape.denote (withExitUB raw lUB) M s ≤ Shape.denote (withExitUB target rUB) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.ExitUB.check_exitUB_iff
    hl hr lUB rUB C prim

/-- A reported capture and machine state violate the lifted shaped order
for the original typed endpoints and their selected continuations. -/
theorem counterexampleExitUB_point (hl : recognizeRouterUnits R raw = some left)
    (hr : recognizeRouterUnits R target = some right) (lUB rUB : Fin L.length → Bool)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states)
    {c : Fin captures} {s : Fin states}
    (found : counterexampleExitUB left right lUB rUB C prim = some (c, s)) :
    let M := model prim (emptyBindings.push (C.capture c))
    ¬ Shape.denote (withExitUB raw lUB) M s ≤ Shape.denote (withExitUB target rUB) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.ExitUB.counterexample_exitUB_point
    hl hr lUB rUB C prim found

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
