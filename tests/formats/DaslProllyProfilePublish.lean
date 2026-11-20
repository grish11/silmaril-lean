module

import Mathlib.Data.String.Basic
import Silmaril.Formats.Dasl.Prolly.Root.Publish.Thms
meta import Silmaril.Formats.Dasl.Prolly.Root.Publish.Thms

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly Silmaril.Semantics

private def leafValue : Shallow Nat := Encode.list.encode [.string "leaf", Encode.list.encode []]
private def bytes : ByteArray := ⟨#[0x82, 0x64, 0x6C, 0x65, 0x61, 0x66, 0x80]⟩
private def conflicting : ByteArray := ⟨#[0xFF]⟩

private def recognizes : Shallow Nat → Bool
  | .list 2 children =>
    match children 0, children 1 with
    | .string label, .list 0 _ => label == "leaf"
    | _, _ => false
  | _ => false

private theorem recognized_value {value : Shallow Nat} (accepted : recognizes value = true) : value = leafValue := by
  unfold recognizes at accepted
  split at accepted
  · rename_i children
    split at accepted
    · rename_i label empty first second
      have named : label = "leaf" := of_decide_eq_true accepted
      subst label
      change Tree.list 2 children = Tree.list 2 _
      congr 1
      funext index
      have atPosition : index = 0 ∨ index = 1 := by omega
      rcases atPosition with rfl | rfl
      · exact first
      · rw [second]
        congr 1
        funext absent
        exact Fin.elim0 absent
    · contradiction
  · contradiction

private def profile (hash? : ByteArray → Option Nat) : RootProfile Nat String Unit :=
  ⟨⟨2, by decide, fun _ _ => false⟩, Encode.text, Encode.null,
    fun value => if recognizes value then some bytes else none, hash?⟩

private def reader (hash? : ByteArray → Option Nat) : (profile hash?).Readback where
  decode? encoded := if encoded = bytes then some leafValue else none
  recovers := by
    intro value encoded success
    change (if recognizes value then some bytes else none) = some encoded at success
    split at success
    · rename_i recognized
      obtain rfl := (Option.some.inj success).symm
      simp [recognized_value recognized]
    · contradiction

private def emptyMap : OrderedMap String Unit := ⟨[], .nil⟩
private def missing : Nat → Option ByteArray := fun _ => none
private def occupied : Nat → Option ByteArray := fun name => if name = 1 then some conflicting else none

public def main : IO Unit := do
  let hash? : ByteArray → Option Nat := fun _ => some 1
  let publisher := (profile hash?).publishMap (reader hash?) emptyMap
  match publisher missing, publisher occupied with
  | .ok (1, staged), .error (.publishing (.collision 1)) =>
    unless staged 1 == some bytes do throw (IO.userError "expected exactly the named bytes")
    match (reader hash?).readBlock? staged 1, publisher staged with
    | some (.leaf []), .ok (1, _) => pure ()
    | _, _ => throw (IO.userError "expected readback and idempotent repeat")
  | _, _ => throw (IO.userError "publication must not replace existing malformed bytes")
  let refused : ByteArray → Option Nat := fun _ => none
  match (profile refused).publishMap (reader refused) emptyMap missing with
  | .error .naming => pure ()
  | _ => throw (IO.userError "unavailable oracle must stop before publication")
