module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Value
open Val (listCheck recordCheck variantCheck optionCheck resultCheck)

inductive Issue where
  | schema (issue : Stored.Issue)
  | endpointNeedsTransfer
  | errorContextNeedsStoreCheck
  | memoryRequired
  | reallocRequired
  | allocationPrecondition
  deriving DecidableEq, Repr

inductive Output where
  | memory (ptr : Nat)
  | flat

def Output.Result : Output → Type
  | .memory _ => Unit
  | .flat => List FlatValue

def Output.needsMemory : Output → Bool
  | .memory _ => true
  | .flat => false

/-- A stored endpoint observation is not authority to transfer it to a guest. -/
def checkSchema (type : TypeOf) : Except Issue Unit := do
  Stored.checkSchema type |>.mapError .schema
  if containsAsyncValue type then throw .endpointNeedsTransfer
  if contains (fun | .errorContext => true | _ => false) type then throw .errorContextNeedsStoreCheck

def checkOptions {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf)
    (output : Output) : Except Issue Unit := do
  let indirect := containsListOrString type
  if (output.needsMemory || indirect) && cx.opts.memory.isNone then throw .memoryRequired
  if indirect && cx.opts.realloc.isNone then throw .reallocRequired

mutual
/-- Check the reference realloc preconditions at every active nested allocation, using
the destination layout, encoding and string retagging mode. Shape is checked by `Payload`. -/
def fits (quirks : Quirks) (encoding : StringEncoding) (width : AddrType) : TypeOf → Val → Bool
  | .prim .string, .string str => decide (StoreStringPre quirks encoding width str)
  | .list type, .list items =>
    decide (StoreListPre (layout width type) items) && items.all (fits quirks encoding width type)
  | .fixedList type _, value => listCheck (fits quirks encoding width type) value
  | .record fields, value => recordCheck (fitsFields quirks encoding width fields) value
  | .tuple types, value => recordCheck (fitsTypes quirks encoding width types) value
  | .variant cases, value => variantCheck (fitsCases quirks encoding width cases) value
  | .option type, value => optionCheck (fits quirks encoding width type) value
  | .result ok err, value => resultCheck (fitsOpt quirks encoding width ok)
      (fitsOpt quirks encoding width err) value
  | .map key type, .list entries =>
    decide (StoreListPre (layout width (.record (mapEntryFields key type))) entries) &&
      entries.all (fun
        | .record [keyValue, value] =>
          (match keyValue with
            | .string str => decide (StoreStringPre quirks encoding width str)
            | _ => true) && fits quirks encoding width type value
        | _ => false)
  | _, _ => true
termination_by structural type => type

def fitsFields (quirks : Quirks) (encoding : StringEncoding) (width : AddrType) :
    List (String × TypeOf) → List Val → Bool
  | [], [] => true
  | (_, type) :: fields, value :: values =>
    fits quirks encoding width type value && fitsFields quirks encoding width fields values
  | _, _ => false
termination_by structural fields => fields

def fitsTypes (quirks : Quirks) (encoding : StringEncoding) (width : AddrType) :
    List TypeOf → List Val → Bool
  | [], [] => true
  | type :: types, value :: values =>
    fits quirks encoding width type value && fitsTypes quirks encoding width types values
  | _, _ => false
termination_by structural types => types

def fitsCases (quirks : Quirks) (encoding : StringEncoding) (width : AddrType) :
    List (String × Option TypeOf) → Nat → Option Val → Bool
  | [], _, _ => false
  | (_, type) :: _, 0, value => fitsOpt quirks encoding width type value
  | _ :: cases, index + 1, value => fitsCases quirks encoding width cases index value
termination_by structural cases => cases

def fitsOpt (quirks : Quirks) (encoding : StringEncoding) (width : AddrType) :
    Option TypeOf → Option Val → Bool
  | none, none => true
  | some type, some value => fits quirks encoding width type value
  | _, _ => false
termination_by structural type => type
end

def emit {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (type : TypeOf) (payload : Payload type) :
    (output : Output) → P E World output.Result
  | .memory ptr => do
    let area := layout width type
    checkAligned ptr area.alignment.bytes
    checkInBounds cx ptr area.size
    Canon.store limits quirks cx payload.val type ptr
  | .flat => lowerFlatAt limits quirks cx width payload.val type

/-- Lower a checked tree payload by running the exact reference effect program.
Only preflight failures are returned as diagnostics; canonical traps remain traps. -/
def lower {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (type : TypeOf) (payload : Payload type) (output : Output) :
    P E World (Except Issue output.Result) :=
  match checkSchema type >>= fun _ => checkOptions cx type output with
  | .error issue => pure (.error issue)
  | .ok () => do
    let width ← ptrType cx
    if !fits quirks cx.opts.encoding width type payload.val then return .error .allocationPrecondition
    return .ok (← emit limits quirks cx width type payload output)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower
