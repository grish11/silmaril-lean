module

import Silmaril.Formats.Dasl.Prolly.Publish.Thms
meta import Silmaril.Formats.Dasl.Prolly.Publish.Thms

open Silmaril Silmaril.Formats.Dasl Silmaril.Semantics.Naming

private def bytes : ByteArray := ⟨#[0xf6]⟩
private def invalidBytes : ByteArray := ⟨#[0xff]⟩
private def empty : Nat → Option ByteArray := fun _ => none
private def existing : Nat → Option ByteArray := fun name => if name = 1 then some invalidBytes else none

private def nullable : Encode.PartialCodec (Shallow Nat) ByteArray where
  encode? value := match value with | .null => some bytes | _ => none
  decode? octets := if octets = bytes then some .null else none
  recovers := by
    intro source target accepted
    cases source <;> simp_all

private def emptyLeaf : Encode.PartialCodec (Semantics.Prolly.Block Nat Nat Unit) (Shallow Nat) where
  encode? value := match value with | .leaf [] => some .null | _ => none
  decode? value := match value with | .null => some (.leaf []) | _ => none
  recovers := by
    intro source target accepted
    cases source with
    | leaf entries =>
      cases entries with
      | nil => simp at accepted; subst target; rfl
      | cons head tail => simp at accepted
    | branch level children => simp at accepted

public def main : IO Unit := do
  let some _ := (admit empty [(3, bytes), (3, bytes)]).toOption | throw (IO.userError "exact repeat rejected")
  match admit existing [(1, bytes)], admit empty [(3, bytes), (3, invalidBytes)] with
  | .error 1, .error 3 => pure ()
  | _, _ => throw (IO.userError "must reject preexisting and intra-batch collisions")
  let tree : Semantics.Prolly.Tree Nat Unit := ⟨0, []⟩
  let publish := Prolly.publish emptyLeaf nullable (fun _ => 1)
  match publish (fun _ => 1) tree empty, publish (fun _ => 1) tree existing, publish (fun _ => 2) tree empty with
  | .ok (1, read), .error (.collision 1), .error (.invalidAddress 1) =>
    unless read 1 == some bytes do throw (IO.userError "the committed block did not roundtrip")
  | _, _, _ => throw (IO.userError "publication must distinguish hash mismatch from raw collision")
