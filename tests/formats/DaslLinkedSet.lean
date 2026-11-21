module

import Silmaril.Formats.Dasl.LinkedSet.Thms
meta import Silmaril.Formats.Dasl.LinkedSet.Thms

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.LinkedSet Silmaril.Formats.Cbor

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def expect {Value : Type} (option : Option Value) (label : String) : IO Value :=
  match option with
  | some value => pure value
  | none => throw (IO.userError label)

private def suite {Name : Type} [DecidableEq Name] (wire : Wire.Profile Name) (blobName : Name → Bool)
    (small large alternate blob missing : Name) : IO Unit := do
  let raw : ByteArray := ⟨#[1]⟩
  let read := Reader.wire wire Encode.bits blobName (fun name =>
    if name = small ∨ name = alternate ∨ name = blob then some raw
    else if name = large then some ⟨#[2]⟩ else none)
  let select : Key → Option (Link Name)
    | [0, 1] => some (.obj small)
    | [0, 2] => some (.obj large)
    | [1, 1] => some (.blob blob)
    | _ => none
  let profile : Profile UInt64 Name := ⟨wire.codec Encode.bits, read, select⟩
  let values : List (Item UInt64) := [.blob raw, .object 2, .object 1, .object 2, .blob raw]
  let layout ← expect (normalize? profile values) "normalize linked semantic values"
  let expected : List (Link Name) := [.obj small, .obj large, .blob blob]
  check (cardinality layout == 3 && decide (layout.entries.map Prod.snd = expected)) "sort by typed payload keys"
  check (decide (layout.lookup? [0, 1] = some (.obj small))) "lookup object by key"
  let rootBytes ← expect (wire.render? (encode layout)) "serialize links"
  let recovered ← expect ((wire.parse? rootBytes).bind (decode? profile)) "recover semantic order from links"
  check (decide (recovered.entries = layout.entries)) "recovered same keys and preferred links"
  for (label, links) in [
      ("name order", [.obj large, .obj small, .blob blob]),
      ("alias of the same object", [.obj alternate, .obj large, .blob blob]),
      ("duplicate object", [.obj small, .obj small]),
      ("unsupported object kind", [.obj blob]),
      ("unsupported blob kind", [.blob small]),
      ("missing block", [.obj missing])] do
    check ((decode? profile (linkList.encode links)).isNone) (label ++ " rejected")
  let collision := { profile with preferred := fun key => if key = [0, 2] then some (.obj small) else select key }
  check ((normalize? collision values).isNone) "same selected name for distinct objects cannot recover both"

private def fixtures (cidProfile : Drisl.CidProfile) (hashCode : UInt8) (wire : Wire.Profile (Drisl.Cid cidProfile)) : IO Unit := do
  let cid kind digest := expect ((Drisl.Cid.codec cidProfile).parse?
    ([1, kind, hashCode, 32] ++ List.replicate 32 digest)) "CID fixture"
  suite wire (fun name => Wire.linkSupported (.blob name))
    (← cid 0x71 9) (← cid 0x71 1) (← cid 0x71 2) (← cid 0x55 3) (← cid 0x71 4)

public def main : IO Unit := do
  fixtures .dasl 0x12 Wire.Profile.dasl
  fixtures .bdasl 0x1e Wire.Profile.bdasl
