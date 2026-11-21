module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Effects.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Execution.Core

/-- The two public gives differ in admission and completion, not in recursive
payload effects. The indirect ABI retains the actual caller's pointer word. -/
inductive GiveEffectRoute where
  | memory (pointer : FlatValue)
  | flat (payload : TypeOf)

namespace GiveEffectRoute

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

def args (handle : BitVec IntType.i32.width) : GiveEffectRoute → List FlatValue
  | .memory pointer => [.int .i32 handle, pointer]
  | .flat _ => [.int .i32 handle]

def action (destination : RecordDestination) : GiveEffectRoute → Action sig
  | .memory _ => .givePayload destination
  | .flat payload => .giveFlat destination payload

def output : GiveEffectRoute → Lower.Output
  | .memory pointer => .memory (flatNat pointer)
  | .flat _ => .flat

def admits (destination : RecordDestination) (tree : OwnedMemory.Tree sig) : GiveEffectRoute → Prop
  | .memory pointer => Stored.flatType pointer = pointerType destination.width
  | .flat payload => rootHasSchema tree payload = true

def reply (destination : RecordDestination) (ticket : Nat) :
    (route : GiveEffectRoute) → Except Endpoints.RecordLower.Issue route.output.Result → Event × List FlatValue
  | .memory _, verdict => completion ticket (verdict.mapError .lowerPayload |>.map (fun _ => 0))
  | .flat payload, verdict => flatCompletion ticket (flatten destination.width payload) (verdict.mapError .lowerPayload)

/-- The recursive effect program resumes the original Core import ticket only
when it returns. A canonical trap never invokes `writeCompletion`. -/
def run (route : GiveEffectRoute) (destination : RecordDestination) (inst : InstId)
    (tree : OwnedMemory.Tree sig) (ticket : Nat) : Session grow sig (Ret (core3 grow)) := do
  let verdict ← Record.Effects.lowerTree recordClaims Limits.spec Quirks.none (destination.context inst) tree route.output
  return .flat (← writeCompletion (route.reply destination ticket verdict))

end GiveEffectRoute

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
