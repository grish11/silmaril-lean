module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Sequence.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

/-- The canonical dynamic collection traversal. The allocation width is read
at entry; the flat descriptor uses the width of the enclosing flat lowering.
The memory descriptor reads the reached width through `storeListDescriptor`. -/
def canonicalDynamic {E : CoreEngine} {World : Type} (cx : LiftLowerContext E)
    (width : AddrType) (element : TypeOf) (entries : List Field)
    (storeEntry : AddrType → Field → Nat → P E World Unit)
    (output : Lower.Output) : P E World output.Result := do
  let reachedWidth ← ptrType cx
  let area := layout reachedWidth element
  let ptr ← allocateListRange cx area entries.length
  elementSequence (fun _ => storeEntry reachedWidth) entries area.size ptr 0
  ListLower.publish cx width ptr entries.length output

/-- Unlike a flat map's despecialized record, the memory map entry uses the
width captured before allocation for both field addresses. `storePrim` still
runs the full canonical key program, including realloc for string keys. -/
def canonicalMapEntry {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (key : WIT.KeyType) (element : TypeOf)
    (entry : Val) (ptr : Nat) : P E World Unit :=
  match entry with
  | .record [keyValue, value] => do
    let area := primitiveLayout width key.toPrimitive
    let keyPtr := alignTo ptr area.alignment
    storePrim limits quirks cx key.toPrimitive keyValue keyPtr
    store limits quirks cx value element (alignTo (keyPtr + area.size) (layout width element).alignment)
  | _ => storeMismatch

/-- Continue only from the live verdict after validating a returned range. A
refusal is a value, not a trap; it never runs element writes or the descriptor. -/
def checkedDynamicContinue {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (width : AddrType) (element : TypeOf)
    (entries : List Field) (index : Nat) (output : Lower.Output) (ptr : Nat) :
    Except Issue Unit → P E World (Except Issue output.Result)
  | .error (.preflight issue) => pure (.error (.field index (.afterAllocation issue)))
  | .error issue => pure (.error (.nested index issue))
  | .ok () => do
    match ← (elementSequence (m := ExceptT Issue (P E World))
      (fun atIndex field addr => ExceptT.mk
        (Internal.runField limits quirks cx authority width field atIndex (.memory addr)))
      entries (layout width element).size ptr 0).run with
    | .error issue => return .error (.nested index issue)
    | .ok () => return .ok (← ListLower.publish cx width ptr entries.length output)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
