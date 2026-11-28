module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Defs
public import Mathlib.Data.List.ProdSigma

/-! # Native packed endpoints with designated UB exits -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

open Syntax (Primitives)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {X : Syntax.Ty} {Γ R L : List Syntax.Ty}
variable {captures seeds results states : Nat}

/-- The continuation for an ordered exit either exposes literal UB or
forwards the incoming payload to the same position. -/
def exitContinuation (selected : Fin L.length → Bool) (i : Fin L.length) :
    Region Φ (L.get i :: Γ) L :=
  if selected i then .ub else .native (jump i rfl (.var 0))

/-- Attach the selected continuations to the original typed native CFG. -/
def withExitUB (raw : Typed Φ Γ L) (selected : Fin L.length → Bool) : Region Φ Γ L :=
  .lsubst (.native raw) (exitContinuation selected)

/-- Only terminal returns to selected positions become fresh top.
Fault states, divergence, and unselected returns remain as computed. -/
def markExitUB (C : Codes X R L captures seeds results) (selected : Fin L.length → Bool) :
    Result results states → Result results states
  | .ret b t => if selected (C.result b).1 then .ub else .ret b t
  | result => result

def Readback.executeExitUB (w : Readback Φ X R L) (selected : Fin L.length → Bool)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states)
    (c : Fin captures) (s : Fin states) : Result results states :=
  markExitUB C selected (w.execute C prim c s)

/-- Find a failing supported capture and state for the decorated endpoints. -/
def counterexampleExitUB (left right : Readback Φ X R L) (leftUB rightUB : Fin L.length → Bool)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states) :
    Option (Fin captures × Fin states) :=
  ((List.finRange captures).product (List.finRange states)).find? fun (c, s) =>
    !decide ((left.executeExitUB leftUB C prim c s).refines (right.executeExitUB rightUB C prim c s))

/-- Decide the finite result order at all coded captures and initial states. -/
def checkExitUB (left right : Readback Φ X R L) (leftUB rightUB : Fin L.length → Bool)
    (C : Codes X R L captures seeds results) (prim : Primitives Φ states) : Bool :=
  (counterexampleExitUB left right leftUB rightUB C prim).isNone

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native
