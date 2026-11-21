module

import Mathlib.Data.String.Basic
import Silmaril.Formats.Dasl.Prolly.Operations.Thms
import Silmaril.Formats.Dasl.Wire.Canonical.Thms
meta import Silmaril.Formats.Dasl.Prolly.Operations.Thms
meta import Silmaril.Formats.Dasl.Wire.Canonical.Thms

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly
open Silmaril.Semantics Silmaril.Semantics.Prolly
open OrderedMap (Overlap)

private def fixtureCid (fill : UInt8) : Option Wire.Cid := do
  let wire := ([0xd8, 0x2a, 0x58, 37, 0, 1, 0x71, 0x12, 32] ++ List.replicate 32 fill).toByteArray
  let .ref (.obj cid) ← Wire.parse? wire | none
  pure cid

private def profile (name? : ByteArray → Option Wire.Cid) : RootProfile Wire.Cid String String :=
  ⟨⟨2, by decide, fun _ _ => false⟩, Encode.text, Encode.text, Wire.renderBounded?, name?⟩

private def reader (name? : ByteArray → Option Wire.Cid) : (profile name?).Readback :=
  ⟨Wire.parse?, fun _ _ hit => Wire.parse_renderBounded hit⟩

private def serialize (block : Block Wire.Cid String String) : Option ByteArray :=
  (encodeBlock Encode.text Encode.text block).bind Wire.renderBounded?

private def rawFixture : IO Unit := do
  let bad := IO.userError "fixture block encoding or decoding"
  let some left := fixtureCid 0 | throw bad
  let some right := fixtureCid 1 | throw bad
  let some output := fixtureCid 2 | throw bad
  let some outputLeft := fixtureCid 3 | throw bad
  let some outputRight := fixtureCid 4 | throw bad
  let some leftBytes := serialize (.leaf [("a", "first"), ("b", "old")]) | throw bad
  let some rightBytes := serialize (.leaf [("b", "new"), ("c", "third")]) | throw bad
  let some outputLeftBytes := serialize (.leaf [("a", "first"), ("b", "new")]) | throw bad
  let some outputRightBytes := serialize (.leaf [("c", "third")]) | throw bad
  let some outputBytes := serialize (.branch 1 [("b", outputLeft), ("c", outputRight)]) | throw bad
  let name? : ByteArray → Option Wire.Cid := fun bytes =>
    ([(leftBytes, left), (rightBytes, right), (outputBytes, output), (outputLeftBytes, outputLeft),
      (outputRightBytes, outputRight)].find? fun pair => pair.1 == bytes).map Prod.snd
  let selected := profile name?
  let readback := reader name?
  let run := selected.combineAndPublish readback .union (Overlap.keepRight (Error := String))
  let raw : Wire.Cid → Option ByteArray := fun name =>
    if name == left then some leftBytes else if name == right then some rightBytes else none
  let .ok (root, staged) := run raw 2 left right | throw (IO.userError "union publication")
  unless root == output && staged left == some leftBytes && staged right == some rightBytes &&
      staged outputLeft == some outputLeftBytes && staged outputRight == some outputRightBytes do
    throw (IO.userError "canonical root and non-replacing publication")
  let codec := blockCodec selected.key selected.payload
  let .ok result := acquire codec (readback.shallowRead staged) 2 2 root | throw (IO.userError "output acquisition")
  unless result.entries == [("a", "first"), ("b", "new"), ("c", "third")]
      && selected.rootName? result == some root do throw (IO.userError "canonical roundtrip")
  let missingChild := fun name => if name == outputRight then none else staged name
  match run missingChild 2 root right with
  | .error (.left (.missing missing)) => unless missing == outputRight do throw bad
  | _ => throw (IO.userError "must not treat a missing branch child as absence")
  match run raw 0 left right with
  | .error (.left (.fuel exhausted)) => unless exhausted == left do throw bad
  | _ => throw (IO.userError "fuel fault lost")
  let malformed := ByteArray.mk #[0xff]
  let badLeft := fun name => if name == left then some malformed else raw name
  match run badLeft 2 left right with
  | .error (.left (.invalidWire observed)) => unless observed == left do throw bad
  | _ => throw (IO.userError "wire fault lost")
  let badRight := fun name => if name == right then some (ByteArray.mk #[0xf6]) else raw name
  match run badRight 2 left right with
  | .error (.right (.invalidNode observed)) => unless observed == right do throw bad
  | _ => throw (IO.userError "node fault lost")
  let occupied := fun name => if name == output then some malformed else raw name
  match run occupied 2 left right with
  | .error (.publish (.publishing (.collision observed))) => unless observed == output do throw bad
  | _ => throw (IO.userError "conflicting occupied name was not rejected")
  match selected.combineAndPublish readback .intersection Overlap.reject raw 2 left right with
  | .error (.overlap "b") => pure ()
  | _ => throw (IO.userError "overlap failure must precede publication")

private def shallowLinkFixture : IO Unit := do
  let key : Encode.TotalCodec Nat (Shallow Nat) := objectLink
  let payload : Encode.TotalCodec Unit (Shallow Nat) := Encode.null
  let codec := blockCodec key payload
  let read : Read Nat := fun name =>
    if name = 10 then (codec.encode? (.leaf [(1, ()), (2, ())])).elim .invalidWire .found
    else if name = 11 then (codec.encode? (.leaf [(2, ()), (3, ())])).elim .invalidWire .found
    else .missing
  let .ok left := acquire codec read 2 1 10 | throw (IO.userError "first linked set acquisition")
  let .ok right := acquire codec read 2 1 11 | throw (IO.userError "second linked set acquisition")
  let overlap := Overlap.discard (Key := Nat) (Payload := Unit) (Error := Nat)
  let .ok result := left.combine .union overlap right | throw (IO.userError "linked set difference")
  unless result.keys == [1, 3] do throw (IO.userError "object links compare by name, not target")

public def main : IO Unit := rawFixture *> shallowLinkFixture
