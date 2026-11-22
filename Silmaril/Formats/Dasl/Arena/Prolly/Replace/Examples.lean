module

import Silmaril.Formats.Dasl.Arena.Prolly.Replace.Thms
import Silmaril.Formats.Dasl.Prolly.LinkKey.Defs
public meta import Silmaril.Formats.Dasl.Arena.Prolly.Replace.Defs
public meta import Silmaril.Formats.Dasl.Prolly.LinkKey.Defs

namespace Silmaril.Formats.Dasl.Arena.Prolly.Indexed.Examples

open Silmaril.Formats.Dasl.Prolly
open Silmaril.Semantics (OrderedMap)
open Silmaril.Semantics.Prolly (Block Policy chunk)

private def raw (tag : Nat) : ByteArray := ⟨#[UInt8.ofNat tag]⟩
private def widthTwo {Key : Type} : Policy Key := ⟨2, by decide, fun _ _ => false⟩

private abbrev Number := Fin UInt64.size
private def number : Encode.TotalCodec Number (Shallow Nat) :=
  (show Encode.TotalCodec Number UInt64 from ⟨UInt64.ofFin, some ∘ UInt64.toFin, fun _ => rfl⟩).then Encode.bits

private def profile : RootProfile Nat Number String :=
  ⟨widthTwo, number, Encode.text, fun shallow =>
    match (blockCodec number Encode.text).decode? shallow with
    | some (.leaf [(1, payload), (3, "c")]) => some (raw (if payload = "new" then 21 else 11))
    | some (.leaf [(7, "y"), (8, "z")]) => some (raw 12)
    | some (.branch 1 [(3, first), (8, 12)]) => some (raw (if first = 21 then 22 else 13))
    | _ => none, fun bytes => bytes.data[0]?.map UInt8.toNat⟩

private def map : OrderedMap Number String :=
  ⟨[(1, "old"), (3, "c"), (7, "y"), (8, "z")], by decide⟩

private def arena : Indexed Nat Number String :=
  ⟨#[.leaf [(1, "old"), (3, "c")], .leaf [(7, "y"), (8, "z")],
    .branch 1 [(3, .local 0), (8, .local 1)]]⟩

private def project : Handle Nat → Nat
  | .local 0 => 11
  | .local 1 => 12
  | .local _ => 13
  | .external name => name

private def rawStore (name : Nat) : Option ByteArray :=
  if name = 11 ∨ name = 12 ∨ name = 13 then some (raw name) else none

private def catchResult {Key : Type} (result : Except (EditError Nat) (Edit Nat Key String × (Nat → Option ByteArray))) :
    Except (EditError Nat) Nat := result.map (fun (edit, _) => edit.root)

#guard profile.rootName? map = some 13
#guard match arena.replaceValue profile project rawStore 2 2 1 "new" with
  | .error _ => false
  | .ok (edit, staged) =>
    decide (edit.named.previous = "old" ∧ edit.root = 4 ∧ edit.project (.local 4) = 22 ∧
      profile.rootName? (RootProfile.replacedMap map 1 "new") = some edit.named.root ∧
      edit.named.writes = [(22, raw 22), (21, raw 21)] ∧ edit.project (.local 2) = 13 ∧
      edit.arena.blocks[4]? = some (.branch 1 [(3, .local 3), (8, .local 1)]) ∧
      edit.arena.blocks[2]? = arena.blocks[2]? ∧ edit.arena.blocks[1]? = arena.blocks[1]? ∧
      staged 13 = rawStore 13 ∧ staged 22 = some (raw 22))

#guard catchResult (arena.replaceValue profile project rawStore 1 2 1 "new") =
  .error (.planning (.read (.fuel (.local 0))))
#guard catchResult (arena.replaceValue profile project rawStore 2 9 1 "new") =
  .error (.planning (.read (.missing (.local 9))))
#guard catchResult (arena.replaceValue profile project rawStore 2 2 2 "new") = .error (.planning .absent)
#guard catchResult (arena.replaceValue profile project (fun name => if name = 22 then some (raw 255) else rawStore name)
  2 2 1 "new") = .error (.collision 22)

private def withExternal : Indexed Nat Number String :=
  ⟨#[.leaf [(1, "old"), (3, "c")], .branch 1 [(3, .local 0), (8, .external 12)]]⟩

#guard catchResult (withExternal.replaceValue profile project rawStore 2 1 1 "new") = .ok 3
#guard catchResult (withExternal.replaceValue profile project rawStore 2 1 8 "new") =
  .error (.planning (.external 12))

private def dangling : Indexed Nat Number String :=
  ⟨#[.leaf [(1, "old"), (3, "c")], .branch 1 [(3, .local 0), (8, .local 2)]]⟩
private def wrongLevel : Indexed Nat Number String := ⟨#[.branch 0 [(1, .external 12)]]⟩

#guard catchResult (dangling.replaceValue profile project rawStore 2 1 1 "new") = .error (.planning (.dangling 1))
#guard catchResult (wrongLevel.replaceValue profile project rawStore 2 0 1 "new") =
  .error (.planning (.read (.invalidNode (.local 0))))

private def objectKey : LinkKey.Mixed Nat := LinkKey.tagged (.obj 7)
private def blobKey : LinkKey.Mixed Nat := LinkKey.tagged (.blob 7)
private def linked : Indexed Nat (LinkKey.Mixed Nat) String :=
  ⟨#[.leaf [(objectKey, "object"), (blobKey, "blob")]]⟩
private def linkedProfile : RootProfile Nat (LinkKey.Mixed Nat) String :=
  ⟨widthTwo, LinkKey.mixed, Encode.text, fun _ => some (raw 80), fun _ => some 80⟩

#guard match linked.replaceValue linkedProfile project rawStore 1 0 blobKey "new blob" with
  | .error _ => false
  | .ok (edit, _) => decide (edit.named.previous = "blob" ∧
      edit.arena.blocks[1]? = some (.leaf [(objectKey, "object"), (blobKey, "new blob")]))

#guard chunk ((widthTwo (Key := Nat)).cut 0) [1, 2, 3, 4, 5, 6] = [[1, 2], [3, 4], [5, 6]]
#guard chunk ((widthTwo (Key := Nat)).cut 0) [0, 1, 2, 3, 4, 5, 6] = [[0, 1], [2, 3], [4, 5], [6]]
#guard chunk ((widthTwo (Key := Nat)).cut 0) [2, 3, 4, 5, 6] = [[2, 3], [4, 5], [6]]

end Silmaril.Formats.Dasl.Arena.Prolly.Indexed.Examples
