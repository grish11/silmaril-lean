module

import Silmaril.Formats.Dasl.StringObjectMap.Index.Thms
meta import Silmaril.Formats.Dasl.StringObjectMap.Index.Defs

open Silmaril Silmaril.Formats.Dasl Silmaril.Formats.Dasl.StringObjectMap

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def checkIndexed : IO Unit := do
  let some layout := (Semantics.OrderedMap.ofEntries?
    [("a", .inline (.ref (.obj 7))), ("b", .linked 7), ("z", .inline (.bool true))] : Option (Layout Nat))
    | throw (IO.userError "ordered fixture")
  let some recovered := codec.decode? (codec.encode layout) | throw (IO.userError "flat round trip")
  check (cardinality recovered == 3) "flat cardinality"
  let wrong := Encode.pairEntry.encode (.string "link", .ref (.blob (7 : Nat)))
  check ((Placement.decode? wrong).isNone) "raw link does not encode a linked object"
  let duplicate := Encode.pairEntry.encode (.string "a", Placement.encode (.linked (7 : Nat)))
  check ((codec.decode? (Encode.list.encode [duplicate, duplicate])).isNone) "duplicate keys rejected"
  let policy : Semantics.Prolly.Policy String := ⟨2, by decide, fun _ _ => false⟩
  let tree := Index.build policy recovered
  check (tree.level == 1) "the fixture spans multiple index blocks"
  let address : Index.Block Nat → Nat := fun
    | .branch _ _ => 10
    | .leaf entries => if entries.head?.map Prod.fst == some "a" then 11 else 12
  let blocks := Semantics.Prolly.blockOccurrences address tree.level tree.root
  let read : Read Nat := fun name =>
    if name == 7 then .found (.i64 42)
    else match (blocks.find? fun block => address block == name).bind Index.blockCodec.encode? with
    | some value => .found value
    | none => .missing
  let root := tree.rootName address
  match Index.lookup read 2 2 root "a", Index.lookup read 2 2 root "b", Index.lookup read 2 2 root "c" with
  | .ok (some (.ref (.obj 7))), .ok (some (.i64 42)), .ok none => pure ()
  | _, _, _ => throw (IO.userError "inline link stays inline, linked value is read, absent key is absent")
  let missingValue : Read Nat := fun name => if name == 7 then .missing else read name
  let invalidValue : Read Nat := fun name => if name == 7 then .invalidWire else read name
  let missingIndex : Read Nat := fun name => if name == 12 then .missing else read name
  match Index.lookup missingValue 2 2 root "b", Index.lookup invalidValue 2 2 root "b",
      Index.lookup missingIndex 2 2 root "c" with
  | .error (.value (.missing 7)), .error (.value (.invalidWire 7)), .error (.index (.missing 12)) => pure ()
  | _, _, _ => throw (IO.userError "read failures must not become absence")

private def checkWire : IO Unit := do
  let cidBytes (kind : UInt8) := [1, kind, 0x12, 0x20] ++ List.replicate 32 0
  let some (.obj name) := Wire.cidCodec.parse? (cidBytes 0x71) | throw (IO.userError "object CID")
  let some (.blob raw) := Wire.cidCodec.parse? (cidBytes 0x55) | throw (IO.userError "raw CID")
  let some layout := (Semantics.OrderedMap.ofEntries? [("a", .inline .null)] : Option (Layout Wire.Cid))
    | throw (IO.userError "ordered wire fixture")
  let some bytes := Wire.render? (codec.encode layout) | throw (IO.userError "flat wire serialization")
  let kind (cid : Wire.Cid) := cid.val[1]? == some 0x71
  let read := readWire kind Wire.parse? (fun _ => some bytes)
  match read name, read raw with
  | .found value, .invalidWire =>
    let some decoded := codec.decode? value | throw (IO.userError "flat wire recovery")
    match lookup decoded read "a" with
    | .ok (some .null) => pure ()
    | _ => throw (IO.userError "wire recovered the wrong value")
  | _, _ => throw (IO.userError "profile must guard object root kind")

public def main : IO Unit := do
  checkIndexed
  checkWire
