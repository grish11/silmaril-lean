module

import Mathlib.Data.String.Basic
import Silmaril.Formats.Dasl.Prolly.Replace.Thms
meta import Silmaril.Formats.Dasl.Prolly.Replace.Thms

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly Silmaril.Formats.Dasl.Prolly.RootProfile
open Silmaril.Semantics.Prolly (Block)

private def profile : RootProfile Nat String String :=
  ⟨⟨2, by decide, fun _ _ => false⟩, Encode.text, Encode.text, fun _ => some ⟨#[42]⟩, fun _ => some 9⟩

private def partialRead : Nat → Except (Fault Nat) (Block Nat String String)
  | 0 => .ok (.branch 1 [("c", 1), ("z", 2)])
  | 1 => .ok (.leaf [("a", "old"), ("c", "same")])
  | 2 => .error (.missing 2)
  | name => .error (.invalidWire name)

public def main : IO Unit := do
  let plan := profile.planReplacement partialRead
  match plan "a" "new" 2 none 0 with
  | .ok result =>
    unless result.previous == "old" && result.root == 9 && result.writes.length == 2 do
      throw (IO.userError "expected one leaf and one ancestor, with the old value")
  | .error _ => throw (IO.userError "the unread sibling must not prevent a selected-path edit")
  match plan "b" "new" 2 none 0, plan "z" "new" 2 none 0, plan "a" "new" 1 none 0,
      plan "a" "new" 1 none 3, plan "a" "new" 1 (some 2) 1 with
  | .error .absent, .error (.read (.missing 2)), .error (.read (.fuel 1)),
      .error (.read (.invalidWire 3)), .error (.read (.invalidNode 1)) => pure ()
  | _, _, _, _, _ => throw (IO.userError "absence, missing, fuel, invalid wire, and invalid node must be distinct")
