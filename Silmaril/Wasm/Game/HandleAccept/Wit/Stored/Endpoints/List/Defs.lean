module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Lower.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.ListLower

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element)

inductive Issue where
  | beforeAllocation (issue : Lower.Issue)
  | afterAllocation (issue : Lower.Issue)
  deriving DecidableEq, Repr

def endpointType : Channel → Element → TypeOf
  | .future, element => .future element
  | .stream, element => .stream element

def preflight {E : CoreEngine} (cx : LiftLowerContext E) (channel : Channel) (element : Element)
    (payload : Payload (.list (endpointType channel element))) (output : Stored.Lower.Output) :
    Except Lower.Issue (List Val × List Lower.Object) := do
  let type := endpointType channel element
  (Stored.checkSchema (.list type)).mapError .schema
  (Stored.Lower.checkOptions cx (.list type) output).mapError .abi
  let .list entries := payload.val | throw .decodedType
  let objects ← entries.mapM (Lower.objects type)
  return (entries, objects.flatten)

/-- The canonical list allocation and range checks. Run endpoint validation again
after realloc: a guest call need not preserve the component or host store. -/
def allocateRange {E : CoreEngine} {World : Type} (cx : LiftLowerContext E)
    (layout : Layout) (count : Nat) : P E World Nat := do
  let size := count * layout.size
  let ptr ← allocate cx layout.alignment.bytes size
  trapIf (decide (ptr ≠ alignTo ptr layout.alignment)) .unalignedPointer
  checkInBounds cx ptr size
  return ptr

/-- Validate the live claim even when called outside list lowering. Spend before
canonical lower takes ownership, not after table insertion: that insertion can
trap after the endpoint's owner has already changed. -/
def transfer {E : CoreEngine} {sig : Signature} (limits : Component.Limits)
    (cx : LiftLowerContext E) (channel : Channel) (element : Element) (id : EndId) :
    P E (State sig) (Except Lower.Issue Nat) := do
  match Lower.prepare (← getStore) (← hostGet) [.endpoint channel element id] with
  | .error issue => return .error issue
  | .ok next =>
    hostSet next
    return .ok (← lowerAsyncValue limits (channel.endKind .read) cx id)

def publish {E : CoreEngine} {World : Type} (cx : LiftLowerContext E) (width : AddrType)
    (ptr count : Nat) : (output : Stored.Lower.Output) → P E World output.Result
  | .flat => pure [ptrFlat width ptr, ptrFlat width count]
  | .memory dest => do
    let size ← ptrSize cx
    storeInt cx ptr dest size
    storeInt cx count (dest + size) size

/-- Lower one dynamic list of claimed endpoints. All typed refusals before realloc are
effect-free. A post-realloc refusal preserves the allocator's effects and performs no
list transfer. During element stores there is no guest call, and claims are spent in
canonical element order even when a later reference operation traps. -/
def lower {E : CoreEngine} {sig : Signature} (limits : Component.Limits)
    (cx : LiftLowerContext E) (channel : Channel) (element : Element)
    (payload : Payload (.list (endpointType channel element))) (output : Stored.Lower.Output) :
    P E (State sig) (Except Issue output.Result) :=
  match preflight cx channel element payload output with
  | .error issue => pure (.error (.beforeAllocation issue))
  | .ok (entries, objects) => do
    match Lower.prepare (← getStore) (← hostGet) objects with
    | .error issue => return .error (.beforeAllocation issue)
    | .ok _ =>
      let width ← ptrType cx
      let layout := layout width (endpointType channel element)
      if !decide (StoreListPre layout entries) then
        return .error (.beforeAllocation (.abi .allocationPrecondition))
      if let .memory ptr := output then
        let dest := ABI.layout width (.list (endpointType channel element))
        checkAligned ptr dest.alignment.bytes
        checkInBounds cx ptr dest.size
      let ptr ← allocateRange cx layout entries.length
      match Lower.prepare (← getStore) (← hostGet) objects with
      | .error issue => return .error (.afterAllocation issue)
      | .ok _ =>
        storeListIntoValidRangeWith layout.size (fun value address => do
          let id ← match channel, value with
            | .future, .future id | .stream, .stream id => pure id
            | _, _ => storeMismatch
          let .ok slot ← transfer limits cx channel element id
            | internal "endpoint list: validated claim changed before element store"
          storeInt cx slot address 4) entries ptr
        return .ok (← publish cx width ptr entries.length output)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.ListLower
