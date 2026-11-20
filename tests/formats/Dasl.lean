module

import Silmaril.Formats.Dasl.Thms
import Silmaril.Formats.Dasl.Encode.Map.Thms
import Silmaril.Formats.Dasl.Measure.Thms
import Silmaril.Formats.Dasl.Prolly.Scan.Thms
import Silmaril.Formats.Dasl.Resolve.Thms
import Silmaril.Formats.Dasl.Resolve.View.Thms
import Silmaril.Formats.Dasl.Wire.Thms
meta import Silmaril.Formats.Dasl.Encode.Map.Thms
meta import Silmaril.Formats.Dasl.Measure.Defs
meta import Silmaril.Formats.Dasl.Prolly.Scan.Defs
meta import Silmaril.Formats.Dasl.Resolve.View.Defs
meta import Silmaril.Formats.Dasl.Wire.Defs

open Silmaril Silmaril.Formats.Dasl Silmaril.Semantics.Naming

open Silmaril.Semantics (OrderedMap OrderedSet)

private def aliases : Relation (Bool × Unit) Unit := graph (fun _ => some ())

example : Binding aliases ∧ ¬ UniqueNames aliases := by
  refine ⟨graph_binding _, fun unique => ?_⟩
  have same : ((false, ()) : Bool × Unit) = (true, ()) := unique rfl rfl
  exact Bool.noConfusion (congrArg Prod.fst same)

private def exampleStore : Store Bool :=
  ⟨graph (fun name => if name then none else some (.ref (.blob true))),
    graph (fun name => if name then some ByteArray.empty else none)⟩

example : ¬ Binding (PartialNames exampleStore) := by
  intro bound
  have opaqueHit : PartialNames exampleStore false (.ref (.blob true)) :=
    ⟨rfl, by constructor <;> intro name payload impossible <;> exact impossible.elim⟩
  have resolved : PartialNames exampleStore false (.blob true ByteArray.empty) := by
    refine ⟨rfl, ⟨?_, ?_⟩⟩
    · intro name payload impossible; exact impossible.elim
    · rintro name payload ⟨rfl, rfl⟩; rfl
  have same := bound opaqueHit resolved
  cases same

private def observations : Partial Nat :=
  .list 2 fun index =>
    .obj 0 (if index.val = 0 then .ref (.blob 1) else .blob 1 ByteArray.empty)

example : observations.LocallyBinding := by
  constructor
  · intro name left right first second
    have canonical (value : Shallow Nat) (hit : observations.bindings.objects name value) :
        value = .ref (.blob 1) := by
      obtain ⟨index, hit⟩ := hit
      change (Partial.bindings (.obj 0 (if index.val = 0 then .ref (.blob 1) else
        .blob 1 ByteArray.empty))).objects name value at hit
      split at hit <;> rcases hit with ⟨_, hit⟩ | impossible <;> first | exact hit | exact impossible.elim
    exact (canonical left first).trans (canonical right second).symm
  · intro name left right first second
    have canonical (value : ByteArray) (hit : observations.bindings.blobs name value) :
        value = ByteArray.empty := by
      obtain ⟨index, hit⟩ := hit
      change (Partial.bindings (.obj 0 (if index.val = 0 then .ref (.blob 1) else
        .blob 1 ByteArray.empty))).blobs name value at hit
      split at hit
      · exact hit.elim
      · exact hit.2
    exact (canonical left first).trans (canonical right second).symm

example : Link.blob 1 ∉ Partial.links false observations := by
  rintro ⟨_, hit⟩
  change Link.blob 1 = Link.obj 0 at hit
  cases hit

example : Link.blob 1 ∈ Partial.links true observations := ⟨0, Or.inr rfl⟩

private def cyclicReader : Reader Bool where
  object? name := if name then some (.ref (.obj true)) else none
  blob? _ := none

private theorem notAccessible {rel : Bool → Bool → Prop} {name : Bool} (loop : rel name name) :
    ¬ Acc rel name := by
  intro accessible
  induction accessible with
  | intro first _ ih => exact ih first loop loop

example : PartialOnly cyclicReader.store true := by
  have observed : cyclicReader.observeRoot? 1 true = some (.obj true (.ref (.obj true))) := rfl
  have loop : Depends cyclicReader.store true true := ⟨.ref (.obj true), rfl, rfl⟩
  refine ⟨⟨_, cyclicReader.observeRoot_sound observed, Or.inl ⟨true, _, Or.inl ⟨rfl, rfl⟩⟩⟩, ?_⟩
  rintro ⟨target, full⟩
  exact notAccessible loop (full.accessible cyclicReader.binding)

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def roundtripI64 (bits : UInt64) (bytes : ByteArray) : IO Unit := do
  check (Wire.render? (.i64 bits) == some bytes) "signed CBOR encoding"
  match Wire.parse? bytes with
  | some (.i64 result) => check (result == bits) "signed CBOR decoding"
  | _ => throw (IO.userError "expected an i64")

private def encodingChecks : IO Unit := do
  let signed : Encode.TotalCodec Int64 (Shallow Nat) := Encode.defaultCodec _ _
  let text : Encode.TotalCodec String (Shallow Nat) := Encode.text
  let bytes : Encode.TotalCodec ByteArray (Shallow Nat) := Encode.bytes
  let fields : Encode.Fields String := ⟨{"message"}, fun _ => "hi"⟩
  let dict := Encode.dictOf text
  let some decoded := dict.decode? (dict.encode fields) | throw (IO.userError "typed dictionary")
  let field := if member : "message" ∈ decoded.keys then some (decoded.values ⟨"message", member⟩) else none
  check (field == some "hi") "typed field"
  match signed.encode (-1) with
  | .i64 bits => check (bits == 0xFFFFFFFFFFFFFFFF) "negative integers preserve their bit pattern"
  | _ => throw (IO.userError "expected i64")
  check ((signed.decode? (.bool false)).isNone) "primitive rejects wrong constructor"
  let blob := Encode.blob
  check ((blob.decode? (Encode.bytes.encode ByteArray.empty)).isNone) "inline bytes are not blobs"
  check ((bytes.decode? (Encode.link.encode (.blob 0))).isNone) "shallow raw link is not inline bytes"
  let pairs := Encode.pairMap text signed
  let records := Encode.recordMap text signed
  let some entries := OrderedMap.ofEntries? [("a", -1), ("b", 2)] | throw (IO.userError "ordered map")
  check (((pairs.decode? (pairs.encode entries)).bind (·.lookup? "a")) == some (-1)) "pair-map lookup"
  check (((records.decode? (records.encode entries)).bind (·.lookup? "b")) == some 2) "record-map lookup"
  check ((pairs.decode? (records.encode entries)).isNone) "pair reader rejects records"
  check ((records.decode? (pairs.encode entries)).isNone) "record reader rejects pairs"
  let makePair (key : String) := Encode.pairEntry.encode (text.encode key, signed.encode 1)
  check ((pairs.decode? (Encode.list.encode [makePair "a", makePair "a"])).isNone) "duplicate decoded keys"
  check ((pairs.decode? (Encode.list.encode [makePair "b", makePair "a"])).isNone) "out-of-order decoded keys"
  check ((records.decode? (Encode.list.encode [.dict {"k", "v", "extra"} (fun _ => .null)])).isNone)
    "only the exact record field set is accepted"
  let sets := Encode.setOf text
  let some keys := OrderedSet.ofKeys? ["a", "b"] | throw (IO.userError "ordered set")
  check (((sets.decode? (sets.encode keys)).map (·.contains "b")) == some true) "set membership"
  check ((sets.decode? (Encode.list.encode [.string "a", .string "a"])).isNone) "duplicate set members"

private def measureChecks : IO Unit := do
  let child : Partial Nat := .obj 7 (.blob 7 ⟨#[10, 20]⟩)
  let tree : Partial Nat := .list 2 fun _ => child
  let blocks := tree.blocks 0
  let encode : Shallow Nat → Option ByteArray := fun _ => some ⟨#[0]⟩
  let sizes : Link Nat → Option Nat := fun | .obj _ => some 1 | .blob _ => some 2
  check (tree.measure .inline == ⟨3, 2, 2, 1⟩) "inline stops at object links"
  check (tree.measure .unfolded == ⟨5, 3, 4, 2⟩) "unfolded counts each repeated target"
  check (blocks.length == 5 && (distinctLinks blocks).card == 3) "distinct identities include the link kind"
  check (occurrenceBytes? encode blocks == some 7) "occurrence bytes"
  check (distinctBytes? sizes blocks == some 4) "distinct bytes"
  check (maxBlockBytes? encode blocks == some 2) "largest block"
  check ((occurrenceBytes? (fun _ => none) blocks).isNone) "serializer failure is not size zero"

open scoped Silmaril.Formats.Dasl.Prolly in
private def prollyChecks : IO Unit := do
  let policy : Semantics.Prolly.Policy Int64 := ⟨2, by decide, fun _ _ => false⟩
  let some map := OrderedMap.ofEntries? [(-2, "left"), (-1, "middle"), (0, "right")]
    | throw (IO.userError "expected signed key order")
  let tree := Semantics.Prolly.build policy map
  check (tree.level == 1 && tree.entries == map.entries) "Prolly builder recovers signed map"
  let byteKeys : Encode.TotalCodec Prolly.ByteKey (Shallow Nat) := Prolly.byteKey
  let some byteMap := OrderedMap.ofEntries? [([0], false), ([0, 255], true), ([255], false)]
    | throw (IO.userError "expected bytewise prefix order")
  let byteMapCodec := Encode.pairMap byteKeys Encode.boolean
  check (((byteMapCodec.decode? (byteMapCodec.encode byteMap)).bind (·.lookup? [0, 255])) == some true)
    "byte-string key roundtrip"
  let codec : Encode.PartialCodec (Semantics.Prolly.Block Nat Int64 String) (Shallow Nat) :=
    Prolly.blockCodec Prolly.intKey Encode.text
  let render := fun block => match codec.encode? block with | some value => Wire.ReadResult.found value | none => .invalidWire
  let sample : Prolly.Read Nat := fun
    | 0 => render (.branch 1 [(-1, 1), (0, 2)])
    | 1 => render (.leaf [(-2, "left"), (-1, "middle")])
    | 2 => render (.leaf [(0, "right")])
    | _ => .missing
  match Prolly.lookup codec sample 2 2 0 (-1), Prolly.lookup codec sample 2 2 0 8 with
  | .ok (some "middle"), .ok none => pure ()
  | _, _ => throw (IO.userError "expected found and verified absence")
  let replaceChild := fun (result : Wire.ReadResult (Shallow Nat)) name => if name = 2 then result else sample name
  match Prolly.lookup codec (replaceChild .missing) 2 2 0 8,
      Prolly.lookup codec (replaceChild .invalidWire) 2 2 0 8,
      Prolly.lookup codec (replaceChild (.found .null)) 2 2 0 8,
      Prolly.lookup codec (replaceChild (render (.leaf [(1, "wrong separator")]))) 2 2 0 8,
      Prolly.lookup codec sample 2 1 0 8 with
  | .error (.missing 2), .error (.invalidWire 2), .error (.invalidNode 2), .error (.invalidNode 0), .error (.fuel 1) => pure ()
  | _, _, _, _, _ => throw (IO.userError "incomplete or invalid Prolly views must not answer")

public def main : IO Unit := do
  encodingChecks
  measureChecks
  prollyChecks
  roundtripI64 0xFFFFFFFFFFFFFFFF ⟨#[0x20]⟩
  roundtripI64 0x8000000000000000 ⟨#[0x3B, 0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]⟩
  roundtripI64 0x7FFFFFFFFFFFFFFF ⟨#[0x1B, 0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]⟩
  let canonical : ByteArray := ⟨#[0xA2, 0x61, 0x62, 0xF5, 0x62, 0x61, 0x61, 0x21]⟩
  let some (.dict keys values) := Wire.parse? canonical | throw (IO.userError "expected dict")
  let inspect (key : String) := if member : key ∈ keys then values ⟨key, member⟩ else .null
  match inspect "b", inspect "aa" with
  | .bool true, .i64 bits => check (bits == 0xFFFFFFFFFFFFFFFE) "dictionary selects named fields"
  | _, _ => throw (IO.userError "dictionary field values changed")
  check (Wire.render? (.dict keys values) == some canonical) "CBOR order sorts encoded keys, not strings"
  check ((Wire.parse? ⟨#[0xA2, 0x61, 0x62, 0xF5, 0x61, 0x62, 0xF4]⟩).isNone) "duplicate key"
  check ((Wire.parse? ⟨#[0xA2, 0x62, 0x61, 0x61, 0x21, 0x61, 0x62, 0xF5]⟩).isNone) "wrong key order"
  check ((Wire.parse? ⟨#[0x18, 0x00]⟩).isNone) "overlong integer"
  check ((Wire.parse? ⟨#[0x1B, 0x80, 0, 0, 0, 0, 0, 0, 0]⟩).isNone) "signed overflow"
  let objBytes := [1, 0x71, 0x12, 32] ++ List.replicate 32 (0 : UInt8)
  let rawBytes := [1, 0x55, 0x12, 32] ++ List.replicate 32 (0 : UInt8)
  let tag (cid : List UInt8) := ([0xD8, 0x2A, 0x58, 37, 0] ++ cid).toByteArray
  let some (.ref (.obj obj)) := Wire.parse? (tag objBytes) | throw (IO.userError "object CID")
  let some (.ref (.blob raw)) := Wire.parse? (tag rawBytes) | throw (IO.userError "raw CID")
  check (Wire.render? (.ref (.obj obj)) == some (tag objBytes)) "object CID roundtrip"
  check (Wire.render? (.ref (.blob raw)) == some (tag rawBytes)) "raw CID roundtrip"
  check ((Wire.render? (.ref (.obj raw))).isNone) "reject wrong kind"
  match Wire.readObject (fun _ => none) obj, Wire.readObject (fun _ => some ⟨#[0xFF]⟩) obj,
      Wire.readObject (fun _ => some canonical) obj, Wire.readObject (fun _ => none) raw with
  | .missing, .invalidWire, .found _, .invalidWire => pure ()
  | _, _, _, _ => throw (IO.userError "object read must distinguish missing and invalid")
  match cyclicReader.observeRoot? 2 true, cyclicReader.observeRoot? 3 false with
  | some (.obj true (.obj true (.ref (.obj true)))), none => pure ()
  | _, _ => throw (IO.userError "bounded view must preserve missing roots and stop at fuel")
