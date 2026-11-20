module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Transcript

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract)

/-- The embedder has the exact typed outcome even when the guest sees only a trap. -/
structure Event where
  call : UCall Nat
  reply : UReply
  outcome : Except Issue (BitVec 32)

abbrev Tag := Silmaril.Accept.IO.Tag Unit Result Unit Unit

/-- Observe every answer at a linked import, including trap replies. An unanswered
redex emits no reply. Entry and exit brackets are still part of the Core session. -/
def roles : Roles Unit Result Unit Unit where
  answerIn := fun _ reply => some reply.result

def replies (tags : List Tag) : List Result :=
  tags.filterMap fun | .inp result => some result | _ => none

def visible (module_ : Module) (events : List Event) : List Result :=
  events.filterMap fun event =>
    if module_.imports[event.call.target]?.isSome then some event.reply.result else none

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

/-- An answer preserves the guest store at call entry, not the store at export entry.
Prevalidation failures leave the entire host state alone. Failures after a load retain
its reference effects but never publish a root or a claim. -/
def Effect (contract : Contract sig) (memory : Option Nat)
    (prior next : World grow sig) (event : Event) : Prop :=
  attempt contract memory prior event.call = (next, event.outcome) ∧
  event.reply.store = event.call.store ∧
  match event.outcome with
  | .error issue =>
    event.reply.result = .trap ∧ next.writer = prior.writer ∧
      match preflight contract memory prior event.call with
      | .error cause => issue = cause ∧ next = prior
      | .ok _ => next.reference = (load contract memory prior event.call).1
  | .ok handle =>
    event.reply.result = .values [.num ⟨.int .i32, handle⟩] ∧
      ∃ root, next.writer.accepted = root :: prior.writer.accepted ∧
        next.writer.held = rootReceipts root ++ prior.writer.held ∧
        next.writer.endpoints = rootEndpoints root ++ prior.writer.endpoints ∧
        handle = BitVec.ofNat 32 (prior.writer.accepted.length + 1)

/-- The host state threads through every completed answer, including refusals. There
is no separate rollback rule at a Core trap or at the next export invocation. -/
inductive Timeline (contract : Contract sig) (memory : Option Nat) (initial : World grow sig) :
    List Event → World grow sig → Prop where
  | start : Timeline contract memory initial [] initial
  | answered {events : List Event} {event : Event} {prior next : World grow sig} :
      Timeline contract memory initial events prior → Effect contract memory prior next event →
      Timeline contract memory initial (events ++ [event]) next

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Transcript
