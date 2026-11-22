module

import Silmaril.Formats.Dasl.Arena.Prolly.Publish.Thms
public meta import Silmaril.Formats.Dasl.Arena.Prolly.Publish.Defs

namespace Silmaril.Formats.Dasl.Arena.Prolly.Publish.Examples

open Silmaril.Formats.Dasl.Prolly (RootProfile)

private def profile : RootProfile Nat String String where
  policy := ⟨4, by decide, fun _ _ => false⟩
  key := Encode.text
  payload := Encode.text
  render? := fun
    | .list length _ => some ⟨#[UInt8.ofNat length]⟩
    | _ => none
  hash? := fun bytes => bytes.data[(0 : Nat)]?.map UInt8.toNat

private def arena : Indexed Nat String String := ⟨#[
  .leaf [("a", "value")], .branch 1 [("a", .local 0), ("z", .external 99)]]⟩

private def only (name : Nat) (bytes : ByteArray) : Nat → Option ByteArray :=
  fun query => if query = name then some bytes else none

private def outcome (profile : RootProfile Nat String String) (fuel : Nat) (read : Nat → Option ByteArray) :
    Except (Fault Nat) Nat := (publish arena profile fuel 1 read).map Prod.fst

#guard outcome profile 1 (fun _ => none) = .error .naming
#guard outcome profile 2 (only 3 ⟨#[255]⟩) = .error (.collision 3)
#guard outcome { profile with hash? := fun _ => some 7 } 2 (fun _ => none) = .error (.collision 7)

#guard match publish arena profile 2 1 (only 2 ⟨#[2]⟩) with
  | .error _ => false
  | .ok (root, updated) =>
    decide (root = 3 ∧ updated 2 = some ⟨#[2]⟩ ∧ updated 3 = some ⟨#[3]⟩ ∧ updated 99 = none) &&
      decide (arena.name? profile.nameBlock? 2 (.local 1) = some root) &&
      decide ((arena.eagerNames profile.nameBlock? 2)[1]? = some (some root))

end Silmaril.Formats.Dasl.Arena.Prolly.Publish.Examples
