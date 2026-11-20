module

public import Mathlib.Data.Finset.Sort
public import Silmaril.Formats.Dasl.Defs
public import Silmaril.Formats.Cbor.Drisl.Model.Defs

/-! Adapter over the existing canonical ATProto DRISL reader and writer. It does not
decode CBOR or multihashes independently. Only shallow objects have wire encodings here. -/

public section

namespace Silmaril.Formats.Dasl.Wire

open Silmaril.Formats.Cbor

abbrev Cid := Drisl.Cid .dasl

@[expose] def IsObjectCid (cid : Cid) : Prop := cid.val[1]? = some 0x71
@[expose] def IsRawCid (cid : Cid) : Prop := cid.val[1]? = some 0x55

@[expose] def ValidLink : Link Cid → Prop
  | .obj cid => IsObjectCid cid
  | .blob cid => IsRawCid cid

@[expose] def cidCodec : Drisl.CidCodec (Link Cid) where
  bytes
    | .obj cid | .blob cid => cid.val
  parse? bytes := do
    let cid ← (Drisl.Cid.codec .dasl).parse? bytes
    if cid.val[1]? = some 0x71 then some (.obj cid)
    else if cid.val[1]? = some 0x55 then some (.blob cid)
    else none

/-- Forget field order. For duplicate entries this keeps the first; the wire reader rejects duplicates. -/
@[expose] def dictFields {Name : Type} : List (String × Shallow Name) →
    (keys : Finset String) × (↥keys → Shallow Name)
  | [] => ⟨∅, fun key => (Finset.notMem_empty _ key.property).elim⟩
  | (key, value) :: tail =>
    let ⟨keys, values⟩ := dictFields tail
    ⟨insert key keys, fun member => if same : member.val = key then value else
      values ⟨member.val, (Finset.mem_insert.mp member.property).resolve_left same⟩⟩

/-- Forget ordered map syntax while retaining typed links and signed integer bit patterns. -/
@[expose] def lower {Name : Type} : {index : JsonIx} →
    RawSyn String (Drisl.Scalar Int64 (Link Name)) index →
    (match index with | .val => Shallow Name | .arr => List (Shallow Name)
                      | .obj => List (String × Shallow Name))
  | _, .scalar (.link name) => .ref name
  | _, .scalar (.data (.number value)) => .i64 value.toUInt64
  | _, .scalar (.data (.bytes payload)) => .bytes payload.toByteArray
  | _, .scalar (.data (.string text)) => .string text
  | _, .scalar (.data (.bool value)) => .bool value
  | _, .scalar (.data .null) => .null
  | _, .list items => let children := lower items; .list children.length children.get
  | _, .map fields => let ⟨keys, values⟩ := dictFields (lower fields); .dict keys values
  | _, .nil => []
  | _, .cons value tail => lower value :: lower tail
  | _, .objNil => []
  | _, .objCons key value tail => (key, lower value) :: lower tail

/-- `parseCbor?` has already rejected duplicate keys, so `lower` forgets order but never
chooses between competing fields. -/
@[expose] def parse? (bytes : ByteArray) : Option (Shallow Cid) :=
  (Drisl.parseCbor? Drisl.i64Cbor cidCodec bytes.data.toList).map lower

@[expose] def toOrdered {Name : Type} : Shallow Name → Drisl.OrderedATProto (Link Name)
  | .ref link => .scalar (.link link)
  | .obj impossible _ | .blob impossible _ => impossible.elim
  | .i64 bits => .scalar (.data (.number bits.toInt64))
  | .bytes payload => .scalar (.data (.bytes payload.data.toList))
  | .string text => .scalar (.data (.string text))
  | .bool value => .scalar (.data (.bool value))
  | .null => .scalar (.data .null)
  | .list _ children => .list (.ofList (List.ofFn fun index => toOrdered (children index)))
  | .dict keys values => .map (.ofEntries (keys.sort.attach.map fun key =>
      (key.val, toOrdered (values ⟨key.val, (Finset.mem_sort _).mp key.property⟩))))

/-- The typed link tag must agree with the CID codec before serialization. The underlying
writer sorts fields by the canonical encoded-key order (not `String` order). -/
def render? (value : Shallow Cid) : Option ByteArray := do
  let ordered := toOrdered value
  if (Drisl.links ordered).all (fun
      | .obj cid => cid.val[1]? == some 0x71
      | .blob cid => cid.val[1]? == some 0x55) then
    (Drisl.renderCbor? Drisl.i64Cbor cidCodec ordered).map List.toByteArray
  else none

/-- A recoverable serialization witness: the writer emits the bytes and the reader
recovers the abstract source. This is not a claim that `render?` is total. -/
@[expose] def Serializes (value : Shallow Cid) (bytes : ByteArray) : Prop :=
  render? value = some bytes ∧ parse? bytes = some value

inductive ReadResult (Payload : Type) where
  | missing
  | invalidWire
  | found (value : Payload)

/-- Read a block requested as an object. A CID of the wrong codec or present but malformed
object bytes is invalid, not missing. Integrity checks belong to the input store. -/
@[expose] def readObject (read : Cid → Option ByteArray) (name : Cid) : ReadResult (Shallow Cid) :=
  if name.val[1]? == some 0x71 then
    match read name with
    | none => .missing
    | some bytes => match parse? bytes with
      | none => .invalidWire
      | some value => .found value
  else .invalidWire

end Silmaril.Formats.Dasl.Wire
