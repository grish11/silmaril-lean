module

public import Silmaril.Wasm.Component.Reference.Canon.Handles.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.ErrorContexts

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

inductive Issue where
  | missingContext
  deriving DecidableEq, Repr

variable {E : CoreEngine} {World : Type}

/-- Reissue an observed error context under a new guest slot. Error contexts are immutable;
unlike endpoints they do not carry a one-shot claim. Check arena membership in the current
store, not an earlier snapshot; a missing object returns an error without allocation. -/
def give (limits : Component.Limits) (cx : LiftLowerContext E) (id : ErrCtxId) :
    P E World (Except Issue Nat) := do
  match (← getStore).errCtx? id with
  | none => pure (.error .missingContext)
  | some _ => do
    let slot ← lowerErrorContext limits cx id
    return .ok slot

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.ErrorContexts
