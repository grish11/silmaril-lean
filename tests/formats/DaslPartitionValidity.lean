module

import Silmaril.Formats.Dasl.Encode.Partition.Validity.Thms
import Silmaril.Formats.Dasl.LinkedSet.Kind.Thms
meta import Silmaril.Formats.Dasl.Encode.Partition.Validity.Thms
meta import Silmaril.Formats.Dasl.LinkedSet.Kind.Thms

open Silmaril.Formats Silmaril.Formats.Cbor Silmaril.Formats.Dasl Silmaril.Semantics
open Silmaril.Formats.Dasl.Encode.Partition

private def separate : OrderedMap Nat Nat := OrderedMap.ofLookupOn {1, 2} some
private def coarse : PER Nat := (PER.universal Nat).restrict (fun key => key ∈ separate.keySet)

private theorem hit_one : separate.lookup? 1 = some 1 := by simp [separate]
private theorem hit_two : separate.lookup? 2 = some 2 := by simp [separate]

example : Sound separate coarse ∧ SameSupport separate coarse ∧ ¬ Exact separate coarse := by
  refine ⟨fun first second edge => ⟨?_, ?_, trivial⟩, fun _ => ?_, fun exactRel => ?_⟩
  · exact (PER.Partition.map_dom_iff_key separate first).mp ((PER.fibers separate.lookup?).dom_left edge)
  · exact (PER.Partition.map_dom_iff_key separate second).mp ((PER.fibers separate.lookup?).dom_right edge)
  · exact ⟨fun hit => ⟨hit, hit, trivial⟩, fun hit => hit.1⟩
  · have related : coarse.rel 1 2 :=
      ⟨(separate.mem_keySet 1).mpr (hit_one ▸ rfl), (separate.mem_keySet 2).mpr (hit_two ▸ rfl), trivial⟩
    change PER.fibers separate.lookup? = coarse at exactRel
    rw [← exactRel] at related
    obtain ⟨_, left, right⟩ := related
    exact (by decide : (1 : Nat) ≠ 2) (Option.some.inj (hit_one.symm.trans (left.trans (right.symm.trans hit_two))))

private def expect {Value : Type} (option : Option Value) (message : String) : IO Value :=
  match option with
  | some value => pure value
  | none => throw (IO.userError message)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checkProfile {Root : Type} [DecidableEq Root] (wire : Wire.Profile Root) (obj blob : Root) : IO Unit := do
  let labels : OrderedMap String String := OrderedMap.ofLookupOn {"alpha", "beta"} (fun _ => some "external")
  let name : Encode.TotalCodec String (Shallow Root) := Encode.text
  let bytes ← expect (wire.render? ((nameMap name).encode labels)) "render finite map"
  let read (root : Root) := if root = obj then some bytes else none
  match observeNamed wire name read obj with
  | .decoded found => check (found.entries == labels.entries) "named map roundtrip"
  | _ => throw (IO.userError "known map did not decode")
  match observeNamed wire name (fun _ => none) obj, observeNamed wire name read blob with
  | .unknown, .rejected => pure ()
  | _, _ => throw (IO.userError "missing name and wrong object kind must be distinct")
  let bad : ByteArray := ⟨#[255]⟩
  match observeNamed wire name (fun _ => some bad) obj with
  | .rejected => pure ()
  | _ => throw (IO.userError "invalid present bytes must be rejected")
  let mixed := LinkedSet.typedLinks (Name := Root) .mixed
  let objectOnly := LinkedSet.typedLinks (Name := Root) .objects
  let blobOnly := LinkedSet.typedLinks (Name := Root) .blobs
  let links := [⟨Link.obj obj, rfl⟩, ⟨Link.blob blob, rfl⟩]
  let ast := mixed.encode links
  check ((mixed.decode? ast).isSome && (objectOnly.decode? ast).isNone && (blobOnly.decode? ast).isNone)
    "mixed link list accepted; strict subsets reject it"
  let raw : ByteArray := ⟨#[1]⟩
  let reader := LinkedSet.Reader.wire wire Encode.bits (fun name => name == blob)
    (fun name => if name = obj ∨ name = blob then some raw else none)
  let sorted : LinkedSet.Profile UInt64 Root := ⟨wire.codec Encode.bits, reader, fun key =>
    if key = [0, 1] then some (.obj obj) else if key = [1, 1] then some (.blob blob) else none⟩
  let objects ← expect (LinkedSet.normalize? sorted [.object 1]) "normalize objects"
  let blobs ← expect (LinkedSet.normalize? sorted [.blob raw]) "normalize blobs"
  let objectLayout ← expect (LinkedSet.narrow? .objects objects) "object-only layout"
  let objectAst := LinkedSet.encodeTyped (LinkedSet.TypedLayout.toMixed .objects objectLayout)
  check ((LinkedSet.decodeTyped? sorted .mixed objectAst).isSome &&
    (LinkedSet.decodeTyped? sorted .blobs objectAst).isNone) "embedding retains sorted object layout"
  check ((LinkedSet.decodeTyped? sorted .blobs (LinkedSet.encode blobs)).isSome &&
    (LinkedSet.decodeTyped? sorted .objects (LinkedSet.encode blobs)).isNone) "sorted blob layout retains tag"

private def fixture (envelope : Drisl.CidProfile) (hash : UInt8) (wire : Wire.Profile (Drisl.Cid envelope)) : IO Unit := do
  let adapter := Drisl.Cid.codec envelope
  let obj ← expect (adapter.parse? ([1, 0x71, hash, 32] ++ List.replicate 32 5)) "object CID"
  let blob ← expect (adapter.parse? ([1, 0x55, hash, 32] ++ List.replicate 32 6)) "blob CID"
  let name : Encode.TotalCodec (Drisl.Cid envelope) (Shallow (Drisl.Cid envelope)) := cidName envelope
  check (name.decode? (name.encode obj) == some obj) "profiled text CID roundtrip"
  checkProfile wire obj blob

public def main : IO Unit := do
  fixture .dasl 0x12 Wire.Profile.dasl
  fixture .bdasl 0x1e Wire.Profile.bdasl
