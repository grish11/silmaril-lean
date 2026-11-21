module

import Silmaril.Formats.Dasl.Mst.Publish.Thms
meta import Silmaril.Formats.Dasl.Mst.Publish.Thms

open Silmaril.Formats.Dasl

private def emptyValue : Shallow Nat :=
  .dict Mst.nodeFields fun member => if member.val = "e" then Encode.list.encode [] else .null

private def recognizes : Shallow Nat → Bool
  | .dict keys values =>
    if same : keys = Mst.nodeFields then
      let fields : ↥Mst.nodeFields → Shallow Nat := same ▸ values
      match fields ⟨"e", by decide⟩, fields ⟨"l", by decide⟩ with
      | .list 0 _, .null => true
      | _, _ => false
    else false
  | _ => false

private theorem recognizes_value {value : Shallow Nat} (hit : recognizes value = true) : value = emptyValue := by
  unfold recognizes at hit
  split at hit
  · rename_i keys values
    split at hit
    · rename_i same
      subst keys
      dsimp at hit
      split at hit
      · rename_i children left right
        change Tree.dict Mst.nodeFields values = _
        unfold emptyValue
        congr 1
        funext member
        have names : member.val = "e" ∨ member.val = "l" := by
          simpa [Mst.nodeFields] using member.property
        rcases names with first | second
        · have eq : member = ⟨"e", by decide⟩ := Subtype.ext first
          rw [eq, left]
          change Tree.list 0 children = Tree.list 0 _
          congr 1
          funext index
          exact Fin.elim0 index
        · have eq : member = ⟨"l", by decide⟩ := Subtype.ext second
          rw [eq, right]
          rfl
      · contradiction
    · contradiction
  · contradiction

private def bytes : ByteArray := ⟨#[0xa2, 0x61, 0x65, 0x80, 0x61, 0x6c, 0xf6]⟩
private def malformed : ByteArray := ⟨#[0xff]⟩

private def codec : Encode.PartialCodec (Shallow Nat) ByteArray where
  encode? value := if recognizes value then some bytes else none
  decode? encoded := if encoded = bytes then some emptyValue else none
  recovers := by
    intro value encoded hit
    change (if recognizes value then some bytes else none) = some encoded at hit
    split at hit
    · rename_i accepted
      obtain rfl := (Option.some.inj hit).symm
      simp [recognizes_value accepted]
    · contradiction

public def main : IO Unit := do
  let profile : Mst.PublishProfile Nat := ⟨codec, fun _ => some 1⟩
  let occupied : Nat → Option ByteArray := fun name => if name = 1 then some malformed else none
  let blank : Nat → Option ByteArray := fun _ => none
  let publish := Mst.Atproto.publish profile []
  match publish blank, publish occupied with
  | .ok (1, staged), .error (.collision 1) =>
    unless staged 1 == some bytes do throw (IO.userError "expected exactly the named bytes")
    let lookup := fun read => Mst.route Mst.Atproto.keyLayer (profile.readShallow read) [0] 1 none 1
    match lookup staged, lookup occupied, lookup blank, publish staged with
    | .ok none, .error (.invalidWire 1), .error (.missing 1), .ok (1, _) => pure ()
    | _, _, _, _ => throw (IO.userError "expected decoded absence, invalid wire, missing and idempotent repeat")
  | _, _ => throw (IO.userError "publication must refuse to replace malformed present bytes")
  let refused : Mst.PublishProfile Nat := ⟨codec, fun _ => none⟩
  match Mst.Atproto.publish refused [] blank with
  | .error .construction => pure ()
  | _ => throw (IO.userError "oracle failure must stop before admission")
