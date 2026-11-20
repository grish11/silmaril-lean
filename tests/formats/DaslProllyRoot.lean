module

import Silmaril.Formats.Dasl.Prolly.Root.Thms
import Silmaril.Formats.Dasl.Wire.Thms
meta import Silmaril.Formats.Dasl.Prolly.Root.Defs
meta import Silmaril.Formats.Dasl.Wire.Defs

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly
open Silmaril.Semantics Silmaril.Semantics.Naming

private def layout : Prolly.Policy String := ⟨2, by decide, fun _ _ => false⟩
private def emptyMap : OrderedMap String Unit := ⟨[], .nil⟩
private def emptyLeafBytes : ByteArray := ⟨#[0x82, 0x64, 0x6C, 0x65, 0x61, 0x66, 0x80]⟩

private def toyProfile (tag : Bool) : RootProfile Bool String Unit :=
  RootProfile.ofTotalHash layout Encode.text Encode.null (fun _ => some emptyLeafBytes) (fun _ => tag)

example : names (toyProfile false).Roots emptyMap.lookup? = {false} ∧
    names (toyProfile true).Roots emptyMap.lookup? = {true} :=
  ⟨((toyProfile false).rootNames_eq_singleton_iff emptyMap false).mpr rfl,
    ((toyProfile true).rootNames_eq_singleton_iff emptyMap true).mpr rfl⟩

private def unavailable : RootProfile Bool String Unit := { toyProfile true with hash? := fun _ => none }

example (name : Bool) : ¬ unavailable.Roots name emptyMap.lookup? :=
  fun proposed => Option.some_ne_none name ((unavailable.roots_iff emptyMap name).mp proposed).symm

private def branched : Prolly.Tree String Unit :=
  ⟨1, [("a", [("a", ())]), ("b", [("b", ())])]⟩

example : branched.rootName? (fun | .leaf _ => none | .branch _ _ => some true) = none := rfl

private def objectCid (fill : UInt8) : Option Wire.Cid :=
  match Wire.parse? (([0xD8, 0x2A, 0x58, 37, 0, 1, 0x71, 0x12, 32] ++ List.replicate 32 fill).toByteArray) with
  | some (.ref (.obj cid)) => some cid
  | _ => none

private def cborProfile (hash : ByteArray → Wire.Cid) : RootProfile Wire.Cid String Unit :=
  RootProfile.ofTotalHash layout Encode.text Encode.null Wire.render? hash

public def main : IO Unit := do
  let some left := objectCid 0 | throw (IO.userError "first object CID")
  let some right := objectCid 1 | throw (IO.userError "second object CID")
  let profile := cborProfile (fun _ => left)
  let alternate := cborProfile (fun _ => right)
  let leaf : Prolly.Block Wire.Cid String Unit := .leaf []
  unless (((encodeBlock profile.key profile.payload leaf).bind profile.render?) == some emptyLeafBytes) do
    throw (IO.userError "empty leaf should serialize to the expected CBOR bytes")
  unless left != right && profile.rootName? emptyMap == some left && alternate.rootName? emptyMap == some right do
    throw (IO.userError "fixed canonical bytes do not identify a naming profile")
  let routed := cborProfile (fun bytes => if bytes.size < 20 then left else right)
  unless branched.rootName? routed.nameBlock? == some right do
    throw (IO.userError "expected leaf links to be rendered before naming the branch")
  let refusesChildren := { routed with hash? := fun bytes => if bytes.size < 20 then none else some right }
  unless (branched.rootName? refusesChildren.nameBlock?).isNone do
    throw (IO.userError "unavailable child names must prevent naming the root")
