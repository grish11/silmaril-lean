module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Syntax
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Transport
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Comparison

import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Divergence

/-! # Exact transport from native readback to the installed overlay evaluator -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

open Syntax (Expr Primitives emptyBindings Bindings.push model)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {X : Syntax.Ty} {R L : List Syntax.Ty}
variable {captures seeds results states : Nat}

/-- The exact syntax comparison also certifies independently proposed tables. -/
theorem sameRegion_eq {Φ : Type u} [DecidableEq Φ] {r t : LambdaSSA.Region Φ} (h : sameRegion r t = true) : r = t :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.sameRegion_eq h

/-- The native router implements the same request and ordered reply map. -/
theorem packedRequestTo_agrees {Γ : List Syntax.Ty} (f : Φ) (arg : Expr Γ (instrSrc f))
    (reply : instrTrg f = LambdaSSA.Region.packedExitType R)
    (target : Fin R.length → Fin L.length) (typed : ∀ i, L.get (target i) = R.get i)
    (M : Shape.Model.{u,0,v,w} Φ Γ) (s : M.raw.σ) :
    Shape.denote (Dependent.packedRequestTo f arg reply target typed) M s =
      Shape.denote (.native (packedRequestTo f arg reply target typed)) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.packedRequestTo_agrees
    f arg reply target typed M.raw s

/-- A successful readback re-emits the original typed region exactly. -/
theorem recognized_eq [DecidableEq Φ] {raw : Typed Φ [X] L} {readback : Readback Φ X R L}
    (accepted : recognize R raw = some readback) : raw = readback.typed :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.recognized_eq accepted

/-- The all-native re-emission and the installed positional overlay evaluator
agree on complete observations in any shaped observational model. -/
theorem readback_agrees (readback : Readback Φ X R L) (M : Shape.Model.{u,0,v,w} Φ [X]) (s : M.raw.σ) :
    Shape.denote (readback.blocks.region readback.start readback.input) M s =
      Shape.denote (.native readback.typed) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.readback_agrees
    readback M.raw s

/-- A generated row certifies the native block recovered at that exact
invocation, with the same final state and ordered label as in the CFG. -/
theorem generated_native_row (readback : Readback Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (p : Fin (seeds * states)) :
    let env := emptyBindings.push (C.capture c)
    let input := C.invocation p
    Shape.denote (.native (readback.routed input.1.1)) ((model prim env).extend input.1.2.property) input.2 =
      (readback.blocks.generate C prim c p).routed C.carrier :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.generated_native_row
    readback C prim c p

/-- The existing finite traversal classifies the actual native CFG at its
original entry, including faults and both forms of ordinary divergence. -/
theorem classify_recognized [DecidableEq Φ] {raw : Typed Φ [X] L} {readback : Readback Φ X R L}
    (accepted : recognize R raw = some readback) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (s : Fin states) :
    Shape.denote (.native raw) (model prim (emptyBindings.push (C.capture c))) s =
      (readback.execute C prim c s).routed C.carrier :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.classify_recognized
    accepted C prim c s

/-- For two successfully read native CFGs at the chosen typed interfaces,
the Boolean result compares their actual entries at every coded start. -/
theorem check_recognized_iff [DecidableEq Φ] {raw target : Typed Φ [X] L}
    {left right : Readback Φ X R L}
    (hl : recognize R raw = some left) (hr : recognize R target = some right)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states) :
    check left right C prim = true ↔ ∀ (c : Fin captures) (s : Fin states),
      let M := model prim (emptyBindings.push (C.capture c))
      Shape.denote (.native raw) M s ≤ Shape.denote (.native target) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.check_recognized_iff
    hl hr C prim

/-- The native silent self-loop has exactly the ordinary-divergence singleton. -/
theorem observe_diverge {Φ : Type u} [HasTy Φ Syntax.Ty] {Γ L : List Syntax.Ty}
    {σ : Type w} (prim : Syntax.StatePrimitives Φ σ) (env : Syntax.Bindings Γ) (s : σ) :
    Shape.denote (.native (diverge (Φ := Φ) (Γ := Γ) (L := L))) (Syntax.model prim env) s =
      WithTop.some {Outcome.diverge} :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native.observe_diverge prim env s

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
