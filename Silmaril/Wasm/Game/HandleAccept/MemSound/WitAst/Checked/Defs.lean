module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Support.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Defs
public import Silmaril.Wasm.Component.Reference.Features.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst

open Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm Silmaril.Wasm.Component
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.Memory

/-- The calling convention for the payload of a `node` import. -/
inductive PayloadPassing where
  | indirect
  | flat
  deriving DecidableEq, Repr

/-- Requested options, checked independently of the payload's WIT type. -/
structure NodeMode where
  address : AddrType := .i32
  encoding : ABI.StringEncoding := .utf8
  passing : PayloadPassing := .indirect
  asynchronous : Bool := false
  deriving DecidableEq, Repr

/-- Runtime resource failures are distinct from an unsupported resource schema. -/
inductive ResourceIssue where
  | unknown (handle : BitVec 32)
  | dead (handle : BitVec 32)
  | wrongType (handle : BitVec 32) (expected actual : Nat)
  | duplicate
  deriving DecidableEq, Repr

/-- The diagnostic of a rejected `node` call. `badPayload` covers malformed nested data,
including nested string/list ranges that exceed the canonical bounds. -/
inductive NodeIssue where
  | payload (issue : PayloadIssue)
  | addressWidth (address : AddrType)
  | flatPayload
  | asyncCall
  | badArguments
  | unknownTag (tag : BitVec 32)
  | missingMemory
  | unalignedPayload
  | unalignedChildren
  | payloadOutOfBounds
  | childrenOutOfBounds
  | childrenTooLong
  | badPayload
  | badChildren
  | badArity
  | resource (issue : ResourceIssue)
  deriving DecidableEq, Repr

/-- The implemented profiles pass synchronous payloads indirectly. -/
def checkNodeMode (mode : NodeMode) : Except NodeIssue Unit := do
  if mode.passing = .flat then throw .flatPayload
  if mode.asynchronous then throw .asyncCall

/-- The raw addresses of a call whose selected schema has passed preflight. -/
structure NodeArgs (Tag : Type) where
  tag : Tag
  payload : Nat
  children : Nat
  count : Nat

variable (S : WitSig) (tagOf : BitVec 32 → Option S.Tag)

/-- Retain the diagnostic at the point where an optional decoding result is required. -/
def requireSome {Error Value : Type} (issue : Error) : Option Value → Except Error Value
  | none => .error issue
  | some value => .ok value

/-- Decode the Core operands without equating a memory32 word with a memory64 word. -/
def nodeOperands : AddrType → List Val → Option (BitVec 32 × Nat × Nat × Nat)
  | .i32, [.num ⟨.int .i32, tag⟩, .num ⟨.int .i32, payload⟩, .num ⟨.int .i32, children⟩,
      .num ⟨.int .i32, count⟩] => some (tag, payload.toNat, children.toNat, count.toNat)
  | .i64, [.num ⟨.int .i32, tag⟩, .num ⟨.int .i64, payload⟩, .num ⟨.int .i64, children⟩,
      .num ⟨.int .i64, count⟩] => some (tag, payload.toNat, children.toNat, count.toNat)
  | _, _ => none

/-- Check the ABI and selected schema before touching the call's memory or resource table. -/
def preflightNode (cap : PayloadCapability) (mode : NodeMode) (o : Callout) :
    Except NodeIssue (NodeArgs S.Tag) := do
  checkNodeMode mode
  let (tag, payload, children, count) ← requireSome .badArguments (nodeOperands mode.address o.args)
  let selected ← requireSome (.unknownTag tag) (tagOf tag)
  (checkPTys cap (S.params selected)).mapError .payload
  return ⟨selected, payload, children, count⟩

/-- Variable lists use the canonical list byte limit. Strings check their own byte limit. -/
def boundedPayloadSegment (o : Callout) (address length : Nat) : Option (List UInt8) :=
  if length ≤ Component.Limits.spec.maxListBytes then
    o.segment address length
  else none

/-- Read only the referenced byte range, after canonical range and alignment checks. -/
def checkedString (encoding : ABI.StringEncoding) (o : Callout) (ptr tagged : Nat)
    (address : AddrType := .i32) : Option String :=
  let range := ABI.loadRange encoding address tagged
  if range.byteLength > ABI.maxStringByteLength then none
  else if ptr ≠ ABI.alignTo ptr range.alignment then none
  else (o.segment ptr range.byteLength).bind range.codec.decode?

/-- WIT observes the decoded text; encoding and code-unit hints belong to the ABI value. -/
def checkedPayloadReader (encoding : ABI.StringEncoding) (o : Callout)
    (address : AddrType := .i32) : PayloadReader :=
  ⟨boundedPayloadSegment o, (fun ptr tagged => checkedString encoding o ptr tagged address), address⟩

/-- The layout/arity portion of decoding after schema validation. In the owning path `S`
here is the raw signature, while preflight checks the original signature. -/
def decodeNodePayload (mode : NodeMode) (args : NodeArgs S.Tag) (o : Callout) :
    Except NodeIssue (Own.Op S × List (BitVec 32)) := do
  if o.mem.isNone then throw .missingMemory
  let types := S.params args.tag
  let layout := valsLayoutFor mode.address types
  if args.payload % layout.alignment.bytes ≠ 0 then throw .unalignedPayload
  if args.children % 4 ≠ 0 then throw .unalignedChildren
  if 4 * args.count > Component.Limits.spec.maxListBytes then throw .childrenTooLong
  let area ← requireSome .payloadOutOfBounds (o.segment args.payload layout.size)
  let reader := checkedPayloadReader mode.encoding o mode.address
  let contents ← requireSome .badPayload (readFieldsWith reader types 0 area)
  let children ← requireSome .childrenOutOfBounds (o.segment args.children (4 * args.count))
  let handles ← requireSome .badChildren (le32s children)
  if (S.arity args.tag).Admits handles.length then return (⟨args.tag, contents⟩, handles)
  else throw .badArity

/-- A plain memory-backed node call; owned fields need the owning entry point. -/
def checkedNode (mode : NodeMode) (o : Callout) :
    Except NodeIssue (Own.Op S × List (BitVec 32)) := do
  let args ← preflightNode S tagOf .memoryOnly mode o
  decodeNodePayload S mode args o

namespace Own

/-- Check liveness and the nominal resource type before taking a representation. -/
def lookupChecked (rt : RT) (resource : Nat) (handle : BitVec 32) : Except ResourceIssue Nat :=
  match rt handle with
  | none => .error (.unknown handle)
  | some entry =>
    if entry.live = false then .error (.dead handle)
    else if entry.ty ≠ resource then .error (.wrongType handle resource entry.ty)
    else .ok entry.rep

/-- Resolve a direct field of an already validated raw schema. -/
def resolveFieldChecked (rt : RT) : (type : PTy) → (ownRaw type).Val → Except ResourceIssue type.Val
  | .own resource, index => lookupChecked rt resource index.toBitVec
  | .bool, value | .s32, value | .u32, value | .s64, value | .u64, value | .string, value
  | .list _, value | .s8, value | .u8, value | .s16, value | .u16, value | .f32, value
  | .f64, value | .char, value | .fixedList _ _, value | .record _, value | .tuple _, value
  | .variant _, value | .enum _, value | .option _, value | .result _ _, value | .flags _, value
  | .borrow _, value => .ok value

/-- Resolve fields against the caller's table without making any changes yet. -/
def resolveFieldsChecked (rt : RT) :
    (types : List PTy) → PTy.Vals (types.map ownRaw) → Except ResourceIssue (PTy.Vals types)
  | [], _ => .ok ()
  | type :: types, (value, values) => do
    let field ← resolveFieldChecked rt type value
    let fields ← resolveFieldsChecked rt types values
    return (field, fields)

/-- Preflight of a raw operation, including the schema, precedes every table move. -/
def resolveOpChecked (rt : RT) (raw : ROp S) : Except NodeIssue (Op S × RT) := do
  (checkPTys .ownFields (S.params raw.1)).mapError .payload
  let handles := movedOp S raw
  if ¬ handles.Nodup then throw (.resource .duplicate)
  let fields ← (resolveFieldsChecked rt (S.params raw.1) raw.2).mapError .resource
  return (⟨raw.1, fields⟩, rt.killAll handles)

/-- An owning node call validates the original schema, then decodes its raw ABI and
resolves it. No table effects are committed on a preflight or decoding error. -/
def checkedOwnNode (mode : NodeMode) (rt : RT) (o : Callout) :
    Except NodeIssue ((Op S × List (BitVec 32)) × RT) := do
  let args ← preflightNode S tagOf .ownFields mode o
  let (raw, children) ← decodeNodePayload (rawSig S) mode args o
  let (value, updated) ← resolveOpChecked S rt raw
  return ((value, children), updated)

/-- Apply the table outcome of a node call. A rejected call returns its typed error and
leaves the **caller** table in place, including all changes from earlier calls. -/
def nodeResult (rt : RT) (outcome : Except NodeIssue ((Op S × List (BitVec 32)) × RT)) :
    Except NodeIssue (Op S × List (BitVec 32)) × RT :=
  match outcome with
  | .error issue => (.error issue, rt)
  | .ok (value, updated) => (.ok value, updated)

end Own

/-- The checked host contract for an addressed Core memory. The actual memory's address
width is checked separately from the requested ABI mode. -/
def checkedCallout (imp : String × String) (memory : Nat) (call : UCall Nat)
    (expected : AddrType := .i32) :
    Except NodeIssue Callout := do
  let mem ← requireSome .missingMemory call.store.mems[memory]?
  if mem.type.address ≠ expected then throw (.addressWidth mem.type.address)
  return ⟨imp, call.args, some mem.bytes⟩

/-- Inspect the diagnostic for a node import before choosing an ABI-level reply. -/
def checkedAt {Value : Type} (mode : NodeMode) (imp : String × String) (memory : Nat)
    (call : UCall Nat) (decode : Callout → Except NodeIssue Value) : Except NodeIssue Value := do
  checkNodeMode mode
  let observed ← checkedCallout imp memory call mode.address
  decode observed

/-- A rejected import traps the current Core call without replacing its store. Successful
imports still obey the caller-supplied writer contract. -/
def checkedReply {Value : Type} (attempt : Except NodeIssue Value) (call : UCall Nat)
    (onSuccess : Value → UReply → Prop) (reply : UReply) : Prop :=
  match attempt with
  | .error _ => reply = ⟨call.store, .trap⟩
  | .ok value => onSuccess value reply

/-- Host reply relation for a memory-only `node` import. -/
def checkedNodeReply (mode : NodeMode) (imp : String × String) (memory : Nat)
    (call : UCall Nat) (onSuccess : Own.Op S × List (BitVec 32) → UReply → Prop) : UReply → Prop :=
  checkedReply (checkedAt mode imp memory call (checkedNode S tagOf mode)) call onSuccess

/-- Host reply relation for a checked owning `node` import. The success continuation
receives the resolved node and the table to use after its move, never a raw index. -/
def checkedOwnReply (mode : NodeMode) (rt : Own.RT) (imp : String × String) (memory : Nat)
    (call : UCall Nat) (onSuccess : (Own.Op S × List (BitVec 32)) × Own.RT → UReply → Prop) :
    UReply → Prop :=
  checkedReply (checkedAt mode imp memory call (Own.checkedOwnNode S tagOf mode rt)) call onSuccess

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
