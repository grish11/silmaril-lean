module

public import Silmaril.Formats.SExp.Family.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs
public import Silmaril.Wasm.Component.Reference.Value.Typing.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Value

abbrev TypeOf := WIT.ClosedType RtId
abbrev Payload (type : TypeOf) := { value : Val // value.HasType type }

/-- An ordinary AST signature whose payloads come from the reference WIT value family.
Endpoint and error-context values name reference arena objects, not Core table indices. -/
structure Signature where
  Tag : Type
  payload : Tag → TypeOf
  arity : Tag → Arity

def Signature.ast (sig : Signature) : AstSig :=
  ⟨sig.Tag, fun tag => Payload (sig.payload tag), sig.arity⟩

abbrev Tree (sig : Signature) := AST sig.ast

inductive Issue where
  | storedBorrow
  | ownedResourceNeedsIdentity
  | malformedType
  | flatTypes
  | decodedType
  | childArity
  deriving DecidableEq, Repr

/-- A closed ABI operand, either a memory address or an exact flat vector. -/
inductive Input where
  | memory (ptr : Nat)
  | flat (values : List FlatValue)

mutual
/-- Look for owners lifted by this value's canonical load. Loading a stream or future
moves only its readable endpoint; its element schema describes a separate, later copy. -/
def payloadContainsOwn : TypeOf → Bool
  | .own _ => true
  | .list t | .fixedList t _ | .option t | .map _ t => payloadContainsOwn t
  | .record fields => payloadFieldsContainOwn fields
  | .tuple types => payloadTypesContainOwn types
  | .variant cases => payloadCasesContainOwn cases
  | .result success failure => payloadOptContainsOwn success || payloadOptContainsOwn failure
  | .prim _ | .borrow _ | .flags _ | .enum _ | .errorContext | .stream _ | .future _ => false
  | .ref impossible => nomatch impossible

def payloadFieldsContainOwn : List (String × TypeOf) → Bool
  | [] => false
  | (_, t) :: rest => payloadContainsOwn t || payloadFieldsContainOwn rest

def payloadTypesContainOwn : List TypeOf → Bool
  | [] => false
  | t :: rest => payloadContainsOwn t || payloadTypesContainOwn rest

def payloadCasesContainOwn : List (String × Option TypeOf) → Bool
  | [] => false
  | (_, t) :: rest => payloadOptContainsOwn t || payloadCasesContainOwn rest

def payloadOptContainsOwn : Option TypeOf → Bool
  | none => false
  | some t => payloadContainsOwn t
end

def checkSchema (type : TypeOf) : Except Issue Unit :=
  if containsBorrow type then .error .storedBorrow
  else if payloadContainsOwn type then .error .ownedResourceNeedsIdentity
  else if ABI.ValType.WellFormedCM type then .ok ()
  else .error .malformedType

def checkValue (type : TypeOf) (value : Val) : Except Issue (Payload type) :=
  if typed : value.HasType type then .ok ⟨value, typed⟩ else .error .decodedType

def flatType : FlatValue → CoreType
  | .int kind _ => .int kind
  | .float kind _ => .float kind

variable {E : CoreEngine} {World : Type}

/-- Check the preconditions asserted by the canonical loaders. After preflight, use
their entire effect programs: a later reference trap does not undo an earlier slot move.
`HasType` is a shape check; nominal identity was checked by the reference lifts. -/
def lift (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (type : TypeOf) (input : Input) : P E World (Except Issue (Payload type)) :=
  match checkSchema type with
  | .error issue => pure (.error issue)
  | .ok () => do
    let width ← ptrType cx
    match input with
    | .memory ptr =>
      let layout := ABI.layout width type
      checkAligned ptr layout.alignment.bytes
      checkInBounds cx ptr layout.size
      return checkValue type (← loadAt limits quirks cx width type ptr)
    | .flat values =>
      if values.map flatType != ABI.flatten width type then return .error .flatTypes
      let (value, _) ← liftFlatAt limits quirks cx width type (FlatCursor.ofList values)
      return checkValue type value

/-- The children are already resolved trees. Check arity before lifting any handles. -/
def buildNode (sig : Signature) (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (tag : sig.Tag) (input : Input) (children : List (Tree sig)) :
    P E World (Except Issue (Tree sig)) := do
  if !(sig.arity tag).Admits children.length then return .error .childArity
  let payload ← lift limits quirks cx (sig.payload tag) input
  return payload.map fun value => AST.node tag value children

/-- Publish an accepted tree in the reference machine's host state. This operation
records observations; it does not lower or copy guest ownership of an endpoint. -/
def record (sig : Signature) (tree : Tree sig) : P E (List (Tree sig)) Unit := do
  hostSet (tree :: (← hostGet))

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored
