module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Effects

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower (Field)

variable {E : CoreEngine} {World : Type} {sig : Signature}

/-- The effect policy at a checked transfer leaf. The canonical leaf sees the
same value and type for both destinations; a spend precedes its canonical effects. -/
def transfer (access : Access E World sig) (field : Field) (index : Nat) :
    P E World (Except RecordLower.Issue Unit) := do
  match field with
  | .owner receipt =>
    match prepareOwner (← access.read) receipt with
    | .error issue => return .error (.nested index issue)
    | .ok _ =>
      access.spendOwner (receiptId receipt)
      return .ok ()
  | .endpoint channel element id =>
    let state ← access.read
    match prepareEndpoint (← getStore) state channel element id with
    | .error issue => return .error (.nested index issue)
    | .ok _ =>
      access.spendEndpoint id
      return .ok ()
  | .context id =>
    let _ ← access.read
    if ((← getStore).errCtx? id).isNone then
      return .error (.field index (.beforeAllocation .missingContext))
    return .ok ()
  | _ => return .ok ()

def canonical (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (field : Field) : (output : Lower.Output) → P E World output.Result
  | .flat => lowerFlatAt limits quirks cx width field.value field.type
  | .memory ptr => store limits quirks cx field.value field.type ptr

def checkedLeaf (access : Access E World sig) (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (field : Field) (index : Nat) (output : Lower.Output) :
    P E World (Except RecordLower.Issue output.Result) := do
  match ← transfer access field index with
  | .error issue => return .error issue
  | .ok () => return .ok (← canonical limits quirks cx width field output)

def reserve (access : Access E World sig) (plan : List RecordLower.Object) :
    P E World (Except RecordLower.Issue Unit) := do
  return prepare (← getStore) (← access.read) plan

section

variable (access : Access E World sig) (limits : Component.Limits) (quirks : Quirks)
  (cx : LiftLowerContext E) (width : AddrType)

mutual
/-- A recursive view of the checked canonical effect program. Each compound
enters its selected children in order, with typed refusal in the return type
and canonical traps in the program. In particular a collection returns from
canonical allocation and range validation before rechecking its live plan. -/
def field : Field → Nat → (output : Lower.Output) → P E World (Except RecordLower.Issue output.Result)
  | .data type payload, index, output => do
    return (← Lower.lower limits quirks cx type payload output).mapError
      (.field index ∘ .beforeAllocation ∘ .abi)
  | item@(.owner _), index, output | item@(.endpoint ..), index, output
  | item@(.context _), index, output => checkedLeaf access limits quirks cx width item index output
  | .aggregate type fields, index, .memory ptr => do
    checkInBounds cx ptr (layout width type).size
    return (← memory fields ptr 0).mapError (.nested index)
  | .aggregate _ fields, index, .flat | .fixed _ _ fields, index, .flat => do
    return (← flat fields 0).mapError (.nested index)
  | .fixed element _ entries, index, .memory ptr => do
    return (← elements entries (layout width element).size ptr 0).mapError
      (.nested index)
  | .dynamic _ element entries, index, output => do
    let plan := Field.listObjects entries
    match ← reserve access plan with
    | .error (.preflight issue) => return .error (.field index (.beforeAllocation issue))
    | .error issue => return .error (.nested index issue)
    | .ok () =>
      let area := layout width element
      let ptr ← allocateListRange cx area entries.length
      match ← reserve access plan with
      | .error (.preflight issue) => return .error (.field index (.afterAllocation issue))
      | .error issue => return .error (.nested index issue)
      | .ok () =>
        match ← elements entries area.size ptr 0 with
        | .error issue => return .error (.nested index issue)
        | .ok () => return .ok (← ListLower.publish cx width ptr entries.length output)
  | .sum type arms tag selected, index, .flat => do
    let joined := (flatten width type).drop 1
    match selected with
    | none => return .ok (← lowerFlatVariantWith arms.length joined tag [] (pure []))
    | some child =>
      match ← field child 0 .flat with
      | .error issue => return .error (.nested index issue)
      | .ok words => return .ok (← lowerFlatVariantWith arms.length joined tag
          (flatten width child.type) (pure words))
  | .sum _ arms tag selected, index, .memory ptr => do
    let address ← storeVariantHead cx arms.length (maxCaseAlignment (arms.map (layoutOption width))) tag ptr
    match selected with
    | none => return .ok ()
    | some child =>
      return (← field child 0 (.memory address)).mapError (.nested index)
termination_by structural item => item

def memory : List Field → Nat → Nat → P E World (Except RecordLower.Issue Unit)
  | [], _, _ => pure (.ok ())
  | child :: rest, cursor, index => do
    let area := layout width child.type
    let ptr := alignTo cursor area.alignment
    match ← field child index (.memory ptr) with
    | .error issue => return .error issue
    | .ok () => memory rest (ptr + area.size) (index + 1)
termination_by structural fields => fields

def elements : List Field → Nat → Nat → Nat → P E World (Except RecordLower.Issue Unit)
  | [], _, _, _ => pure (.ok ())
  | child :: rest, stride, ptr, index => do
    match ← field child index (.memory ptr) with
    | .error issue => return .error issue
    | .ok () => elements rest stride (ptr + stride) (index + 1)
termination_by structural fields => fields

def flat : List Field → Nat → P E World (Except RecordLower.Issue (List FlatValue))
  | [], _ => pure (.ok [])
  | child :: rest, index => do
    match ← field child index .flat with
    | .error issue => return .error issue
    | .ok words =>
      let headWords : List FlatValue := words
      return (← flat rest (index + 1)).map (headWords ++ ·)
termination_by structural fields => fields
end

/-- Root placement checks are part of the effect program, not part of typed
preflight. They run even if no child touches guest memory. -/
def root (type : TypeOf) (item : Field) (output : Lower.Output) :
    P E World (Except RecordLower.Issue output.Result) := do
  if let .memory ptr := output then
    let area := layout width type
    checkAligned ptr area.alignment.bytes
    checkInBounds cx ptr area.size
  field access limits quirks cx width item 0 output

end

/-- The effect view of a selected tree payload, including preflight. Children
of the accepted tree are not lowered as part of giving its root payload. -/
def lowerTree (access : Access E World sig) (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (tree : Tree sig) (output : Lower.Output) :
    P E World (Except RecordLower.Issue output.Result) :=
  match tree with
  | .atom impossible => impossible.elim
  | .tag payload _ _ =>
    let type := sig.payload payload.1
    RecordLower.Internal.lowerWithPlan quirks cx (authority access limits cx) type payload.2.val.value
      (preflightValue cx type payload.2 output) Field.objects
      (fun width item => root access limits quirks cx width type item output)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Effects
