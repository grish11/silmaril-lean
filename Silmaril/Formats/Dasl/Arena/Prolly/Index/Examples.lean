module

import Silmaril.Formats.Dasl.Arena.Prolly.Index.Thms
import Silmaril.Formats.Dasl.Prolly.LinkKey.Defs
public meta import Silmaril.Formats.Dasl.Arena.Prolly.Index.Defs
public meta import Silmaril.Formats.Dasl.Prolly.LinkKey.Defs
public meta import Silmaril.Formats.Dasl.Prolly.Scan.Defs

namespace Silmaril.Formats.Dasl.Arena.Prolly.Index.Examples

open Silmaril.Formats.Dasl.Prolly (Fault)
open Silmaril.Semantics.Prolly (Block)

private def named : Resident Nat String String :=
  ⟨[(10, .ok (.branch 1 [("a", 20), ("z", 30)])), (20, .ok (.leaf [("a", "resident")]))]⟩

private def localizeChild : Nat → Option Nat
  | 20 => some 0
  | _ => none

private def acquire : Option (Indexed Nat String String × Nat) := do
  let (withLeaf, _) ← ((Indexed.empty.acquire named.read (fun _ => none) 20).toOption).join
  ((withLeaf.acquire named.read localizeChild 10).toOption).join

private def query (fuel : Nat) (key : String) : Except (Fault (Handle Nat)) (Option String) :=
  match acquire with
  | none => .error (.invalidNode (.local 1))
  | some (arena, root) => arena.lookup named.read 4 fuel root key

private def choose : Block Nat String String → Option Nat
  | .leaf [("a", "resident")] => some 20
  | .branch 1 [("a", 20), ("z", 30)] => some 10
  | _ => none

private def namesAgree : Bool :=
  match acquire with
  | none => false
  | some (arena, root) => arena.name? choose 2 (.local root) == some 10 &&
    arena.name? choose 1 (.local root) == none && (arena.eagerNames choose 2)[root]? == some (some 10)

private def forwardRejected : Bool :=
  ((Indexed.empty : Indexed Nat String String).append? (.branch 1 [("a", .local 0)])).isNone

#guard query 2 "a" = .ok (some "resident")
#guard query 2 "z" = .error (.missing (.external 30))
#guard query 2 "zz" = .ok none
#guard query 1 "a" = .error (.fuel (.local 0))
#guard namesAgree
#guard forwardRejected

private def linkKeysDistinct : Bool :=
  let blobKey : Prolly.LinkKey.Mixed Nat := Prolly.LinkKey.tagged (.blob 7)
  let objectKey : Prolly.LinkKey.Mixed Nat := Prolly.LinkKey.tagged (.obj 7)
  match Indexed.empty.append? (.leaf [(blobKey, "blob")]) with
  | none => false
  | some (arena, index) =>
    let missing : Reader Nat (Prolly.LinkKey.Mixed Nat) String := fun absent => .error (.missing absent)
    match arena.lookup missing 4 1 index blobKey, arena.lookup missing 4 1 index objectKey with
    | .ok (some payload), .ok none => payload == "blob"
    | _, _ => false

#guard linkKeysDistinct

end Silmaril.Formats.Dasl.Arena.Prolly.Index.Examples
