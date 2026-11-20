module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Resources.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Lower.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Value

abbrev Receipt := (resource : RtId) × Resources.Owned resource

/-- A reference value observed together with the real identities of its owned leaves.
Receipts follow the active leaves in canonical traversal order; representations are not keys.
This observation does not itself authorize a second transfer. -/
structure Observed where
  value : Val
  owners : List Receipt

def Observed.ordinary (value : Val) : Observed := ⟨value, []⟩

def Observed.aggregate (ctor : List Val → Val) (items : List Observed) : Observed :=
  ⟨ctor (items.map Observed.value), items.flatMap Observed.owners⟩

def Observed.variant (index : Nat) (payload : Option Observed) : Observed :=
  ⟨.variant index (payload.map Observed.value), (payload.map Observed.owners).getD []⟩

def Observed.own (resource : RtId) (identity : HandleObjId) (rep : Nat) : Observed :=
  ⟨.own rep, [⟨resource, ⟨identity, rep⟩⟩]⟩

def Receipt.requirement (receipt : Receipt) : RtId × Nat :=
  (receipt.1, receipt.2.representation)

mutual
/-- The ordered nominal types and representations at the active owner leaves of a
typed value. This describes where receipts belong; it does not grant ownership. -/
def ownerRequirements : TypeOf → Val → List (RtId × Nat)
  | .own resource, .own representation => [(resource, representation)]
  | .list type, .list values | .fixedList type _, .list values => values.flatMap (ownerRequirements type)
  | .record types, .record values => fieldRequirements types values
  | .tuple types, .record values => tupleRequirements types values
  | .variant cases, .variant tag value => caseRequirements cases tag value
  | .option type, .variant 1 (some value) => ownerRequirements type value
  | .result success _, .variant 0 value => optionalRequirements success value
  | .result _ failure, .variant 1 value => optionalRequirements failure value
  | .map _ type, .list entries => entries.flatMap fun
    | .record [_, value] => ownerRequirements type value
    | _ => []
  | _, _ => []
termination_by structural type => type

def fieldRequirements : List (String × TypeOf) → List Val → List (RtId × Nat)
  | (_, type) :: types, value :: values => ownerRequirements type value ++ fieldRequirements types values
  | _, _ => []
termination_by structural types => types

def tupleRequirements : List TypeOf → List Val → List (RtId × Nat)
  | type :: types, value :: values => ownerRequirements type value ++ tupleRequirements types values
  | _, _ => []
termination_by structural types => types

def caseRequirements : List (String × Option TypeOf) → Nat → Option Val → List (RtId × Nat)
  | (_, type) :: _, 0, value => optionalRequirements type value
  | _ :: cases, tag + 1, value => caseRequirements cases tag value
  | [], _, _ => []
termination_by structural cases => cases

def optionalRequirements : Option TypeOf → Option Val → List (RtId × Nat)
  | some type, some value => ownerRequirements type value
  | _, _ => []
termination_by structural type => type
end

def Observed.Complete (observed : Observed) (type : TypeOf) : Prop :=
  observed.owners.map Receipt.requirement = ownerRequirements type observed.value

abbrev Payload (type : TypeOf) :=
  { observed : Observed // observed.value.HasType type ∧ observed.Complete type }

def ast (sig : Signature) : AstSig :=
  ⟨sig.Tag, fun tag => Payload (sig.payload tag), sig.arity⟩

abbrev Tree (sig : Signature) := AST (ast sig)

inductive Issue where
  | schema (issue : Stored.Issue)
  | incompleteReceipts
  deriving DecidableEq, Repr

def checkSchema (type : TypeOf) : Except Stored.Issue Unit :=
  if containsBorrow type then .error .storedBorrow
  else if ABI.ValType.WellFormedCM type then .ok ()
  else .error .malformedType

variable {E : CoreEngine} {World : Type}

/-- Interpret only owner leaves differently from the ordinary memory load. `takeWith` uses
the identity returned by the reference removal; no handle slot is reread or reconstructed. -/
def carrier (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E) :
    LoadCarrier E World Observed :=
  let ref : LoadCarrier E World Val := .reference limits quirks cx
  { prim := fun prim ptr => Observed.ordinary <$> ref.prim prim ptr
    flags := fun labels ptr => Observed.ordinary <$> ref.flags labels ptr
    own := fun resource ptr => do
      let slot := (← loadInt cx ptr 4).toNat
      Resources.takeWith cx resource slot (Observed.own resource)
    borrow := fun resource ptr => Observed.ordinary <$> ref.borrow resource ptr
    stream := fun type ptr => Observed.ordinary <$> ref.stream type ptr
    future := fun type ptr => Observed.ordinary <$> ref.future type ptr
    errorContext := fun ptr => Observed.ordinary <$> ref.errorContext ptr
    list := Observed.aggregate Val.list
    record := Observed.aggregate Val.record
    variant := Observed.variant }

/-- Use the same receipt operation for direct slots and slots in indirect memory payloads. -/
def flatCarrier (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : Silmaril.Wasm.AddrType) : FlatLoadCarrier E World Observed :=
  let ref : FlatLoadCarrier E World Val := .reference limits quirks cx width
  { memory := carrier limits quirks cx
    prim := fun prim cursor => Prod.map Observed.ordinary id <$> ref.prim prim cursor
    flags := fun flags => Observed.ordinary (Val.flags flags)
    own := fun resource slot => Resources.takeWith cx resource slot (Observed.own resource)
    borrow := fun resource slot => Observed.ordinary <$> ref.borrow resource slot
    stream := fun type slot => Observed.ordinary <$> ref.stream type slot
    future := fun type slot => Observed.ordinary <$> ref.future type slot
    errorContext := fun slot => Observed.ordinary <$> ref.errorContext slot }

/-- Component argument lifting with receipts for the one-pointer spill as well as
the direct flat vector. `projectFlatValues` identifies the entire program after erasure. -/
def liftFlatValuesWith {Result : Type} (limits : Component.Limits) (cx : LiftLowerContext E)
    (leaves : Silmaril.Wasm.AddrType → FlatLoadCarrier E World Result) (max : Nat)
    (cursor : FlatCursor) (types : List (WIT.ClosedType RtId)) :
    P E World (List Result × FlatCursor) := do
  let width ← ptrType cx
  if (flattenTypes width types).length > max then
    let (ptr, next) ← cursor.next (pointerType width)
    let shape := layout width (.tuple types : WIT.ClosedType RtId)
    trapIf (decide (flatNat ptr ≠ alignTo (flatNat ptr) shape.alignment)) .unalignedPointer
    checkInBounds cx (flatNat ptr) shape.size
    let values ← loadTypesAtWith limits cx width (leaves width).memory types (flatNat ptr)
    return (values, next)
  else
    liftFlatTypesWith limits cx width (leaves width) types cursor

/-- The caller's reference start protocol with an observing argument lift. -/
def lowerOnStartWith {Result : Type}
    (liftArgs : LiftLowerContext E → Nat → FlatCursor → List (WIT.ClosedType RtId) →
      P E World (List Result × FlatCursor)) (caller : CallerId) : P E World (List Result) := do
  match ← getObj ArenaField.callers caller with
  | .lower subtask cx args pos ft maxParams _ =>
    maybeOnProgress subtask
    modifyStore (LowerSt.startSt subtask)
    let (values, next) ← liftArgs cx maxParams ⟨args, pos⟩ (ft.params.map (·.2))
    modifyStore (LowerSt.setCallerPosSt caller next.pos)
    return values
  | _ => internal "lowerOnStart: not a canon_lower caller record"

/-- Observe owners during the canonical lower caller's start callback, including parameters
spilled to memory. This is an observation of the reference callback, not a storage boundary:
its other values, including borrows, retain their original reference scopes. -/
def observeLowerOnStart (limits : Component.Limits) (quirks : Quirks) (caller : CallerId) :
    P E World (List Observed) :=
  lowerOnStartWith (fun cx => liftFlatValuesWith limits cx (flatCarrier limits quirks cx)) caller

def checkValue (type : TypeOf) (value : Observed) : Except Issue (Payload type) :=
  if typed : value.value.HasType type then
    if complete : value.owners.map Receipt.requirement =
        ownerRequirements type value.value then .ok ⟨value, typed, complete⟩
    else .error .incompleteReceipts
  else .error (.schema .decodedType)

/-- Check the whole schema before lifting a handle. Once lifting starts, failures
have reference trap semantics, not the Core checked import's call-local rejection semantics. -/
def lift (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (type : TypeOf) (input : Input) : P E World (Except Issue (Payload type)) :=
  match checkSchema type with
  | .error issue => pure (.error (.schema issue))
  | .ok () => do
    let width ← ptrType cx
    match input with
    | .memory ptr => do
      let layout := ABI.layout width type
      checkAligned ptr layout.alignment.bytes
      checkInBounds cx ptr layout.size
      let value ← loadAtWith limits cx width (carrier limits quirks cx) type ptr
      return checkValue type value
    | .flat values =>
      if values.map flatType != ABI.flatten width type then return .error (.schema .flatTypes)
      let (value, _) ← liftFlatAtWith limits cx width (flatCarrier limits quirks cx width) type
        (FlatCursor.ofList values)
      return checkValue type value

def buildNode (sig : Signature) (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (tag : sig.Tag) (input : Input) (children : List (Tree sig)) :
    P E World (Except Issue (Tree sig)) := do
  if !(sig.arity tag).Admits children.length then return .error (.schema .childArity)
  let payload ← lift limits quirks cx (sig.payload tag) input
  return payload.map fun value => AST.node tag value children

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
