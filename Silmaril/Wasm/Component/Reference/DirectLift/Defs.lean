module

public import Silmaril.Wasm.Component.Reference.Calls.Thms
public import Silmaril.Wasm.Execution.Core.Entry.Defs
public import Silmaril.Wasm.Game.Strategy.Defs

@[expose] public section

namespace Silmaril.Wasm.Component.Reference.DirectLift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.SingleThreaded
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

/-- Flat, synchronous, resource-free canonical ABI. `wellFormed` concerns the current
shared store, not a new instantiation. -/
structure Boundary {P : Profile} (I : ScalarInstance)
    (shared : Store (CanonHost (core3P P))) (x : SimpleExport)
    (args : List Silmaril.Wasm.Component.Val) (question : I.F.Op) : Prop where
  wellFormed : I.WellFormed (Store.mapH (fun _ => 0) shared)
  noImports : I.imports = []
  signature : I.exports.get question.1 = fnOf x.ty.flat
  arguments : question.2.val = (lowerArgs x.ty.params args).map ofFlat
  typed : ValTy.checkList x.ty.params args = true
  floatFreeParams : floatFreeList x.ty.params = true
  floatFreeResults : floatFreeList x.ty.results = true
  flatParams : (ValTy.flatList x.ty.params).length ≤ 16
  oneResult : x.ty.results.length ≤ 1
  flatResults : (ValTy.flatList x.ty.results).length ≤ 1

/-- A successful lift reports the loaded component values. A trap can come from Core
(including an uncaught exception) or from rejecting the values of a normal Core return. -/
def Reports (x : SimpleExport) : CallOutcome → Result → Prop
  | .resolved (some values), .values coreValues =>
    ∃ ys ws, coreValues.mapM toFlat? = some ys ∧
      liftArgs x.ty.results ys = some ws ∧ values = ws.map toRefVal
  | .trap, .trap | .trap, .throw _ => True
  | .trap, .values coreValues =>
    ∃ ys, coreValues.mapM toFlat? = some ys ∧ liftArgs x.ty.results ys = none
  | _, _ => False

end Silmaril.Wasm.Component.Reference.DirectLift
