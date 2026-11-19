module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst

open Silmaril.Formats Silmaril.Wasm.Component

/-- Resource capabilities of stored tree payloads, independent of the ABI or a particular table. -/
inductive PayloadCapability where
  | memoryOnly
  | ownFields
  deriving DecidableEq, Repr

/-- Why a schema is unavailable at the stored-tree boundary. -/
inductive PayloadIssue where
  | requiresResourceTable (resource : Nat)
  | nestedOwn (resource : Nat)
  | storedBorrow (resource : Nat)
  | future
  | stream
  | errorContext
  | unresolvedType
  | mapNeedsDespecialization
  deriving DecidableEq, Repr

universe u

variable {Ref : Type u}

mutual
/-- Check the whole type, not just the active branch of a value. `atField` means a
direct field of the node payload vector; no compound subfield inherits that capability. -/
def checkPayload (cap : PayloadCapability) (atField : Bool) :
    WIT.ValType Ref Nat → Except PayloadIssue Unit
  | .prim _ | .enum _ | .flags _ => .ok ()
  | .list type | .fixedList type _ | .option type => checkPayload cap false type
  | .record fields => checkPayloadFields cap fields
  | .tuple types => checkPayloads cap false types
  | .variant cases => checkPayloadCases cap cases
  | .result value failure => do
      checkPayloadOpt cap value
      checkPayloadOpt cap failure
  | .own resource =>
      if !atField then .error (.nestedOwn resource)
      else match cap with
        | .memoryOnly => .error (.requiresResourceTable resource)
        | .ownFields => .ok ()
  | .borrow resource => .error (.storedBorrow resource)
  | .future _ => .error .future
  | .stream _ => .error .stream
  | .errorContext => .error .errorContext
  | .ref _ => .error .unresolvedType
  | .map _ _ => .error .mapNeedsDespecialization

/-- Validate each field of a positional vector in order. -/
def checkPayloads (cap : PayloadCapability) (atField : Bool) :
    List (WIT.ValType Ref Nat) → Except PayloadIssue Unit
  | [] => .ok ()
  | type :: types => do
      checkPayload cap atField type
      checkPayloads cap atField types

/-- Validate every field of a nested record. -/
def checkPayloadFields (cap : PayloadCapability) :
    List (String × WIT.ValType Ref Nat) → Except PayloadIssue Unit
  | [] => .ok ()
  | (_, type) :: fields => do
      checkPayload cap false type
      checkPayloadFields cap fields

/-- Validate every case of a variant, including cases inactive in any particular value. -/
def checkPayloadCases (cap : PayloadCapability) :
    List (String × Option (WIT.ValType Ref Nat)) → Except PayloadIssue Unit
  | [] => .ok ()
  | (_, type) :: cases => do
      checkPayloadOpt cap type
      checkPayloadCases cap cases

/-- Validate an optional compound payload type. -/
def checkPayloadOpt (cap : PayloadCapability) : Option (WIT.ValType Ref Nat) → Except PayloadIssue Unit
  | none => .ok ()
  | some type => checkPayload cap false type
end

/-- Check a `PTy` signature with the same rules used for broader WIT types. -/
def checkPTys (cap : PayloadCapability) (types : List PTy) : Except PayloadIssue Unit :=
  checkPayloads (Ref := Empty) cap true (Wit.toWitList types)

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
