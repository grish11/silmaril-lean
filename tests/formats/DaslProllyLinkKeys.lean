module

import Silmaril.Formats.Dasl.Prolly.LinkKey.Thms
import Silmaril.Formats.Dasl.Wire.Canonical.Thms
meta import Silmaril.Formats.Dasl.Prolly.LinkKey.Thms
meta import Silmaril.Formats.Dasl.Wire.Canonical.Thms

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly
open Silmaril.Semantics

private abbrev Key := LinkKey.Mixed Nat

private def first : Key := LinkKey.tagged (.obj 7)
private def aliasKey : Key := LinkKey.tagged (.obj 8)
private def blobKey : Key := LinkKey.tagged (.blob 7)
private def missingKey : Key := LinkKey.tagged (.blob 9)

private def mapCodec := blockCodec (Name := Nat) LinkKey.mixed Encode.text

private def read (targets : Bool) : Read Nat := fun name =>
  if name = 20 then (mapCodec.encode? (.leaf [(first, "old"), (aliasKey, "alias")])).elim .invalidWire .found
  else if name = 21 then (mapCodec.encode? (.leaf [(first, "new"), (blobKey, "blob")])).elim .invalidWire .found
  else if targets && (name == 7 || name == 8) then .found .null
  else .missing

private def fixture (targets : Bool) : IO Unit := do
  let bad := IO.userError "mixed link key fixture"
  let .ok left := acquire mapCodec (read targets) 2 1 20 | throw bad
  let .ok right := acquire mapCodec (read targets) 2 1 21 | throw bad
  let .ok result := left.combine .union (OrderedMap.Overlap.keepRight (Error := Unit)) right | throw bad
  unless result.entries == [(first, "new"), (aliasKey, "alias"), (blobKey, "blob")] do throw bad
  let some singleton := OrderedMap.ofEntries? [(first, "new")] | throw bad
  unless singleton.domainSubset left && !singleton.submap left && result.cardinality == 3 do throw bad
  let .ok .none := routedLookup mapCodec (read targets) 2 1 21 missingKey | throw bad
  let .error (.missing 22) := routedLookup mapCodec (read targets) 2 1 22 missingKey | throw bad
  let some leftSet := (OrderedMap.ofEntries? [(first, ()), (aliasKey, ())] : Option (LinkKey.Set Nat)) | throw bad
  let some rightSet := (OrderedMap.ofEntries? [(first, ()), (blobKey, ())] : Option (LinkKey.Set Nat)) | throw bad
  let .ok symmetric := OrderedSet.combine .union (OrderedMap.Overlap.discard (Error := Unit)) leftSet rightSet | throw bad
  let .ok disjoint := OrderedSet.combine .intersection (OrderedMap.Overlap.discard (Error := Unit)) leftSet rightSet | throw bad
  unless symmetric.keys == [aliasKey, blobKey] && disjoint.keys.isEmpty do throw bad

private instance : LinearOrder Wire.Cid :=
  LinearOrder.lift' (fun cid => cid.val.map UInt8.toFin) (fun _ _ same =>
    Subtype.ext (List.map_injective_iff.mpr (fun _ _ hit => UInt8.toFin_inj.mp hit) same))

private def cid? (codec fill : UInt8) : Option Wire.Cid := do
  let wire := ([0xd8, 0x2a, 0x58, 37, 0, 1, codec, 0x12, 32] ++ List.replicate 32 fill).toByteArray
  let .ref link ← Wire.parse? wire | none
  match link with
  | .obj name | .blob name => some name

private def rawFixture : IO Unit := do
  let bad := IO.userError "mixed link key raw publication fixture"
  let some left := cid? 0x71 0 | throw bad
  let some right := cid? 0x71 1 | throw bad
  let some output := cid? 0x71 2 | throw bad
  let some target := cid? 0x71 8 | throw bad
  let some blob := cid? 0x55 8 | throw bad
  let objectKey := LinkKey.tagged (.obj target)
  let blobKey := LinkKey.tagged (.blob blob)
  let render := fun entries => (encodeBlock LinkKey.mixed Encode.null (.leaf entries)).bind Wire.renderBounded?
  let some leftBytes := render [(objectKey, ())] | throw bad
  let some rightBytes := render [(blobKey, ())] | throw bad
  let some outputBytes := render [(objectKey, ()), (blobKey, ())] | throw bad
  let selected := LinkKey.profile LinkKey.mixed Encode.null ⟨2, by decide, fun _ _ => false⟩
    Wire.renderBounded? (fun bytes => if bytes == outputBytes then some output else none)
  let reader : selected.Readback := ⟨Wire.parse?, fun _ _ hit => Wire.parse_renderBounded hit⟩
  let raw := fun name => if name == left then some leftBytes else if name == right then some rightBytes else none
  let run := selected.combineAndPublish reader .union (OrderedMap.Overlap.keepLeft (Error := Unit))
  let .ok (published, staged) := run raw 1 left right | throw bad
  unless published == output && staged published == some outputBytes && staged target == none && staged blob == none do throw bad
  let codec := blockCodec selected.key selected.payload
  let .ok result := acquire codec (reader.shallowRead staged) 2 1 published | throw bad
  unless result.keys == [objectKey, blobKey] && selected.rootName? result == some published do throw bad
  let occupied := fun name => if name == output then some ByteArray.empty else raw name
  match run occupied 1 left right with
  | .error (.publish (.publishing (.collision name))) => unless name == output do throw bad
  | _ => throw bad

public def main : IO Unit := fixture false *> fixture true *> rawFixture
