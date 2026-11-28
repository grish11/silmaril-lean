module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Inference.Defs

/-! Run equality-only entry discovery before the singleton two-route check. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Staged

open RVSDG (Tuple)
open Discovery.MemRef.CF (Programs)
open Retained.Load.Static.Sequence.Search

variable {args : List ValueSort} {cells : Nat}

inductive RouteOutcome (cells : Nat) (args : List ValueSort) where
  | entryNotSingleton
  | routesRefused
  | applied (artifacts : Artifacts cells args)

structure Result (cells : Nat) (args : List ValueSort) where
  entryOnly : Emission cells args
  route : RouteOutcome cells args

/-- Keep the initial emitter's original artifact. A successful route cut
supplies the final optimized artifact. Both refusals keep the entry-only pair. -/
def Result.programs (result : Result cells args) : Programs cells args :=
  match result.route with
  | .applied artifacts => { result.entryOnly.programs with optimized := artifacts.optimized }
  | .entryNotSingleton | .routesRefused => result.entryOnly.programs

def checkRoutes (cells : Nat) (graph : Graph args) (entry : Memory.Graph args) : RouteOutcome cells args :=
  match Static.lower cells graph entry with
  | some artifacts => .applied artifacts
  | none =>
    if (Composition.asPrefixStore entry).isSome then .routesRefused
    else .entryNotSingleton

/-- Check the actual residual table from equality-only discovery. -/
def lower (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args) :
    Except InvocationError (Result cells args) := do
  let stage ← Inference.lower graph entry input
  pure ⟨stage, checkRoutes cells graph stage.entry⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Staged
