module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Collection.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.CanonicalTree

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

/-- Memory maps use the width read before allocating the entry array for both
key and value placement. All other arrays store entries as ordinary values. -/
inductive EntryMode where
  | value
  | memoryMap (width : AddrType) (key : WIT.KeyType) (element : TypeOf)

def EntryMode.forOutput (reached : AddrType) (type : TypeOf) (output : Lower.Output) : EntryMode :=
  match type, output with
  | .map key element, .memory _ => .memoryMap reached key element
  | _, _ => .value

def leaf {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (item : Field) : (output : Lower.Output) → P E World output.Result
  | .flat => lowerFlatAt limits quirks cx width item.value item.type
  | .memory ptr => store limits quirks cx item.value item.type ptr

section

variable {E : CoreEngine} {World : Type}
variable (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E) (width : AddrType)

mutual
/-- Factor the reference canonical program at the compiled tree's boundaries.
This view does not add authority. It retains the position of each width read,
allocation, range trap, child program and descriptor write. -/
def field : Field → (output : Lower.Output) → P E World output.Result
  | .aggregate _ children, .flat | .fixed _ _ children, .flat => flat children
  | .aggregate _ children, .memory ptr => memory children ptr
  | .fixed element _ children, .memory ptr => do
    let reached ← ptrType cx
    elements children .value (layout reached element).size ptr
  | .dynamic type element children, output => do
    let reached ← ptrType cx
    let area := layout reached element
    let ptr ← allocateListRange cx area children.length
    elements children (EntryMode.forOutput reached type output) area.size ptr
    ListLower.publish cx width ptr children.length output
  | .sum type arms tag selected, .flat =>
    lowerFlatVariantWith arms.length ((flatten width type).drop 1) tag
      (match selected with | none => [] | some child => flatten width child.type)
      (match selected with | none => pure [] | some child => field child .flat)
  | .sum _ arms tag selected, .memory ptr => do
    let reached ← ptrType cx
    let address ← storeVariantHead cx arms.length (maxCaseAlignment (arms.map (layoutOption reached))) tag ptr
    match selected with
    | none => pure ()
    | some child => field child (.memory address)
  | item@(.data ..), output | item@(.endpoint ..), output
  | item@(.owner _), output | item@(.context _), output => leaf limits quirks cx width item output
termination_by structural item => item

def flat : List Field → P E World (List FlatValue)
  | [] => pure []
  | child :: rest => do
    let words : List FlatValue ← field child .flat
    return words ++ (← flat rest)
termination_by structural fields => fields

def memory : List Field → Nat → P E World Unit
  | [], _ => pure ()
  | child :: rest, cursor => do
    let reached ← ptrType cx
    let area := layout reached child.type
    let ptr := alignTo cursor area.alignment
    field child (.memory ptr)
    memory rest (ptr + area.size)
termination_by structural fields => fields

def elements : List Field → EntryMode → Nat → Nat → P E World Unit
  | [], _, _, _ => pure ()
  | child :: rest, .value, stride, ptr => do
    field child (.memory ptr)
    elements rest .value stride (ptr + stride)
  | .aggregate _ [keyField, valueField] :: rest, mode@(.memoryMap reached _ _), stride, ptr => do
    let keyArea := layout reached keyField.type
    let keyPtr := alignTo ptr keyArea.alignment
    field keyField (.memory keyPtr)
    field valueField (.memory (alignTo (keyPtr + keyArea.size) (layout reached valueField.type).alignment))
    elements rest mode stride (ptr + stride)
  | child :: rest, mode@(.memoryMap reached key element), stride, ptr => do
    canonicalMapEntry limits quirks cx reached key element child.value ptr
    elements rest mode stride (ptr + stride)
termination_by structural fields => fields
end

end

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.CanonicalTree
