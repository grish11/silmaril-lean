module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Stored.Endpoints.RecordLower

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {pointer : FlatValue}

abbrev ParkedShape := AggregateShape (fun field => ∃ item : StringField, item.field = field)

/-- The placed branch compares the public body up to its real reply
continuation, not a delivered reply or event. Allocator prefixes are
compared under the callback classification of the linked scheduler. -/
def ParkedBody (call : PayloadRoot.Site grow sig (.memory pointer)) (depth : Nat) (next : call.ReferenceNext)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig)) : Prop :=
  let older : ReturnFrame.Substitutions (core3 grow) (HostState sig) := fun _ _ => False
  nested profile ready bindings older call.destination call.inst depth call.field
    0 (flatNat pointer) call.checked (call.reference next) call.cursor call.cursor call.reply next
    (fun reached reference check canon =>
      ChildFrameOver older reached reference check canon ∧
      reached.ctl = check.control (call.reply (.ok ())) ∧ reference.ctl = canon.control (next ()))

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence
