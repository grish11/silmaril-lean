module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Inference.Defs

/-! Run static entry discovery before checking the actual final Store. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Staged

open RVSDG (Tuple)
open Discovery.MemRef.CF (Programs)
open Memory.DeadStore.Search.Selection.Readers.Repeat (storeCount)
open Retained.Load.Static.Sequence.Search

variable {args : List ValueSort} {cells : Nat}

/-- Nominate the current last Store version if the final-Store checker
admits its shape. -/
def find (entry : Memory.Graph args) : Option Nat :=
  let version := storeCount entry
  (Final.cut version entry).map fun _ => version

inductive RouteOutcome (cells : Nat) (args : List ValueSort) where
  | noFinalCandidate
  | routesRefused (version : Nat)
  | applied (version : Nat) (artifacts : Artifacts cells args)

structure Result (cells : Nat) (args : List ValueSort) where
  entryOnly : Emission cells args
  route : RouteOutcome cells args

/-- Reuse the initial emitter's original artifact and the route emitter's
optimized artifact on success. Both refusals keep the entry-only pair. -/
def Result.programs (result : Result cells args) : Programs cells args :=
  match result.route with
  | .applied _ artifacts => { result.entryOnly.programs with optimized := artifacts.optimized }
  | .noFinalCandidate | .routesRefused _ => result.entryOnly.programs

def checkRoutes (cells : Nat) (graph : Graph args) (entry : Memory.Graph args) : RouteOutcome cells args :=
  match find entry with
  | none => .noFinalCandidate
  | some version =>
    match Final.lower cells graph entry version with
    | none => .routesRefused version
    | some artifacts => .applied version artifacts

/-- Discover entry cuts, then find and check the final Store in the
resulting table. -/
def lower (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args) :
    Except InvocationError (Result cells args) := do
  let stage ← Inference.lower graph entry input
  pure ⟨stage, checkRoutes cells graph stage.entry⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Staged
