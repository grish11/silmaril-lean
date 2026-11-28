module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Defs

/-! Reorder the two existing cut projections of a flat firing log. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Blocks (Bank)
open Silmaril.MLIR.Arith (Width)
open RVSDG.NestedTheta.Petri (Marking finished pending)
open RVSDG.NestedTheta.Petri.Replay (checkFire markingDecEq)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (iterateThenReturnWith)

/-- Keep the projected states at precisely the changes of that projection. -/
def changes {A B : Type} [DecidableEq B] (view : A → B) (start : A) : List A → List B
  | [] => []
  | next :: tail =>
    if view start = view next then changes view next tail
    else view next :: changes view next tail

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)

abbrev entryTail := iterateThenReturnWith (thetaBody p) p.result
  (endWires (entryCode (src := src) (entry := entry)))

abbrev ThetaMark := Marking semantics (entryTail p)

def prefixChanges (roots : List (RootMark p)) : List (PreMark p) :=
  letI := markingDecEq semantics colourEq (preheader p)
  changes ((entryCut p).observe semantics) (pending semantics (emitted p)) roots

/-- The complete θ marking history with consecutive repetitions erased.
It retains the live child markings and the exact carried colours. -/
def thetaChanges (roots : List (RootMark p)) : List (ThetaMark p) :=
  letI := markingDecEq semantics colourEq (entryTail p)
  changes ((entryCut p).rest semantics) (pending semantics (emitted p)) roots

def finalPreheader (roots : List (RootMark p)) : PreMark p :=
  (entryCut p).observe semantics (roots.getLastD (pending semantics (emitted p)))

def prefixFirst (roots : List (RootMark p)) : List (RootMark p) :=
  (prefixChanges p roots).map fun pre => (entryCut p).attach semantics pre (pending semantics (entryTail p))

def thetaAfter (roots : List (RootMark p)) : List (RootMark p) :=
  (thetaChanges p roots).map ((entryCut p).attach semantics (finalPreheader p roots))

/-- Put all preheader publications before θ entry, preserving the order
of changes within each actual cut projection. -/
def normalize (roots : List (RootMark p)) : List (RootMark p) :=
  prefixFirst p roots ++ thetaAfter p roots

variable (input : Bank (regs := regs) model)

def checkSteps (start : RootMark p) : List (RootMark p) → Bool
  | [] => true
  | next :: tail =>
    (checkFire semantics colourEq (emitted p) input PUnit.unit start next).isSome &&
      checkSteps next tail

/-- A complete original firing log, with no full-publication premise at θ entry. -/
def FireComplete (roots : List (RootMark p)) : Prop :=
  List.IsChain (RootFire p input) (pending semantics (emitted p) :: roots) ∧
    (finished semantics (emitted p) input PUnit.unit (roots.getLastD (pending semantics (emitted p)))).isSome

/-- Recheck the original log before reordering, so normalization cannot
make a malformed or incomplete input appear valid. -/
def scanNormalized (roots : List (RootMark p)) : Option (Complete p input (normalize p roots)) :=
  let start := pending semantics (emitted p)
  if checkSteps p input start roots &&
      (finished semantics (emitted p) input PUnit.unit (roots.getLastD start)).isSome then
    scan p input (normalize p roots)
  else none

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log
