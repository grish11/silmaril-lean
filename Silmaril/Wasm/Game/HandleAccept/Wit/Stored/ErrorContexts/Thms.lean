module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.ErrorContexts.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.ErrorContexts

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {World : Type}

/-- No effects follow the store lookup for a missing object; otherwise the copy
retains the canonical allocation program, including its traps. -/
theorem give_program (limits : Component.Limits) (cx : LiftLowerContext E) (id : ErrCtxId) :
    (give limits cx id : P E World _) = Prog.op (S := Eff E World) .get (fun store =>
      match store.errCtx? id with
      | none => Prog.pure (.error .missingContext)
      | some _ => (lowerErrorContext limits cx id).bind (fun slot => Prog.pure (.ok slot))) := rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.ErrorContexts
