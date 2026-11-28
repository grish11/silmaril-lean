module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Syntax
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Transport
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Refinement

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration (Result)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
  (Primitives emptyBindings Bindings.push model)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Codes generated_row classify_region)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration (routed_order)

universe u

variable {Φ : Type u} [HasTy Φ (Silmaril.Ty Empty)]
variable {X : Silmaril.Ty Empty} {R L : List (Silmaril.Ty Empty)}
variable {captures seeds results states : Nat}

theorem generated_native_row (w : Readback Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (p : Fin (seeds * states)) :
    let env := emptyBindings.push (C.capture c)
    let input := C.invocation p
    Shape.denote (.native (w.routed input.1.1)) ((model prim env).extend input.1.2.property) input.2 =
      (w.blocks.generate C prim c p).routed C.carrier := by
  let M := model prim (emptyBindings.push (C.capture c))
  let input := C.invocation p
  exact (routed_agrees w input.1.1 (M.extend input.1.2.property).raw input.2).symm.trans
    (generated_row w.blocks C prim c p)

theorem classify_recognized [DecidableEq Φ] {raw : Typed Φ [X] L} {w : Readback Φ X R L}
    (accepted : recognize R raw = some w) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (s : Fin states) :
    Shape.denote (.native raw) (model prim (emptyBindings.push (C.capture c))) s =
      (w.execute C prim c s).routed C.carrier := by
  rw [recognized_eq accepted]
  exact (readback_agrees w (model prim (emptyBindings.push (C.capture c))).raw s).symm.trans
    (classify_region w.blocks C prim c w.start w.input s)

theorem check_recognized_iff [DecidableEq Φ] {raw target : Typed Φ [X] L}
    {left right : Readback Φ X R L}
    (hl : recognize R raw = some left) (hr : recognize R target = some right)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states) :
    check left right C prim = true ↔ ∀ (c : Fin captures) (s : Fin states),
      let M := model prim (emptyBindings.push (C.capture c))
      Shape.denote (.native raw) M s ≤ Shape.denote (.native target) M s := by
  simp only [check, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
  refine forall_congr' fun c => forall_congr' fun s => ?_
  rw [classify_recognized hl C prim c s, classify_recognized hr C prim c s]
  exact (routed_order C.carrier _ _).symm

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
