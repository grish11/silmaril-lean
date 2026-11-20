module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Audit

open Silmaril.Formats Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game

inductive Outcome where
  | rejected (issue : NodeIssue)
  | declined
  | committed
  | other

structure Event where
  target : Nat
  args : List Val
  result : Result
  outcome : Outcome

/-- The newest answered import is at the head. Merely reaching a call has no entry. -/
structure Journal (Q : Type) where
  host : State Q
  entries : List Event := []

variable {S : WitSig} {Q : Type}

/-- Classify an actual checked reply against the state at the reached import. A preflight
refusal is distinct from a writer declining a well-formed node. -/
def observe (K : Contract S Q) (memory : Option Nat) (before : State Q)
    (call : UCall Nat) (reply : UReply) : Event :=
  ⟨call.target, call.args, reply.result,
    if call.target = K.code then
      match K.attempt memory before.resources call with
      | .error issue => .rejected issue
      | .ok _ => match reply.result with
        | .trap => .declined
        | _ => .committed
    else .other⟩

/-- Add a journal entry at precisely the checked answer transition. This cannot introduce
an extra reply or change the Core result, resource effects, or writer transition. -/
def env (K : Contract S Q) (memory : Option Nat) : SEnv UImp :=
  ⟨Journal Q, fun before call reply after =>
    Answer K memory before.host call reply after.host ∧
      after.entries = observe K memory before.host call reply :: before.entries,
    fun _ _ => False⟩

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Audit
