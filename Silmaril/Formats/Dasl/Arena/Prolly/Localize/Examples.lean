module

import Silmaril.Formats.Dasl.Arena.Prolly.Localize.Thms
import Silmaril.Formats.Dasl.Prolly.LinkKey.Defs
public meta import Silmaril.Formats.Dasl.Arena.Prolly.Localize.Defs
public meta import Silmaril.Formats.Dasl.Prolly.LinkKey.Defs

namespace Silmaril.Formats.Dasl.Arena.Prolly.Localize.Examples

open Silmaril.Semantics.Prolly (Block)
open Silmaril.Formats.Dasl.Prolly (blockCodec readBlock)

private def ordinary : Reader Nat String String :=
  readBlock (blockCodec Encode.text Encode.text) fun name =>
    let codec : BlockCodec Nat String String := blockCodec Encode.text Encode.text
    let encode (block : Block Nat String String) := (codec.encode? block).elim .invalidWire .found
    match name with
    | 1 => encode (.branch 1 [("a", 2), ("z", 3)])
    | 2 | 7 => encode (.leaf [("a", "first")])
    | 3 => encode (.leaf [("z", "last")])
    | 4 => encode (.branch 1 [("a", 2), ("m", 5)])
    | 5 => encode (.leaf [("m", "other")])
    | 6 => .found .null
    | 8 => .invalidWire
    | 9 => encode (.branch 1 [("z", 3), ("a", 2)])
    | 11 => encode (.branch 1 [("a", 2), ("z", 10)])
    | _ => .missing

private def empty : Table Nat String String := .empty

#guard match empty.checkedRoot ordinary 4 2 1 [2, 3, 2, 1] with
  | .error _ => false
  | .ok (table, root) =>
    decide (table.arena.blocks.size = 3 ∧ table.locate 2 = some 0 ∧ table.origin 0 = some 2 ∧ root = 2) &&
      decide (table.arena.lookup ordinary 4 2 root "a" = .ok (some "first")) &&
      decide (table.arena.lookup ordinary 4 2 root "b" = .ok none)

#guard match empty.checkedRoot ordinary 4 2 1 [2, 3, 1] with
  | .error _ => false
  | .ok (initial, oldRoot) => match initial.checkedRoot ordinary 4 2 4 [2, 5, 4, 7] with
    | .error _ => false
    | .ok (later, newRoot) =>
      decide (later.arena.blocks.size = 6 ∧ oldRoot = 2 ∧ newRoot = 4) &&
        decide (later.locate 2 = some 0 ∧ later.locate 7 = some 5) &&
        decide (later.arena.lookup ordinary 4 2 oldRoot "z" = .ok (some "last")) &&
        decide (later.arena.lookup ordinary 4 2 newRoot "m" = .ok (some "other"))

#guard ((empty.checkedRoot ordinary 4 2 1 [3, 1]).map Prod.snd) = .error (.unplanned 1)
#guard ((empty.checkedRoot ordinary 4 2 1 [2, 3]).map Prod.snd) = .error (.unplanned 1)
#guard ((empty.checkedRoot ordinary 4 1 1 [2, 3, 1]).map Prod.snd) = .error (.read (.fuel 2))
#guard ((empty.checkedRoot ordinary 4 2 6 []).map Prod.snd) = .error (.read (.invalidNode 6))
#guard ((empty.checkedRoot ordinary 4 2 8 []).map Prod.snd) = .error (.read (.invalidWire 8))
#guard ((empty.checkedRoot ordinary 4 2 9 []).map Prod.snd) = .error (.read (.invalidNode 9))
#guard ((empty.checkedRoot ordinary 4 2 10 []).map Prod.snd) = .error (.read (.missing 10))
#guard ((empty.checkedRoot ordinary 4 2 11 [2, 11]).map Prod.snd) = .error (.read (.missing 10))

private def blob : Prolly.LinkKey.Mixed Nat := Prolly.LinkKey.tagged (.blob 7)
private def obj : Prolly.LinkKey.Mixed Nat := Prolly.LinkKey.tagged (.obj 7)

private def linked : Reader Nat (Prolly.LinkKey.Mixed Nat) String :=
  readBlock (blockCodec Prolly.LinkKey.mixed Encode.text) fun name =>
    let codec : BlockCodec Nat (Prolly.LinkKey.Mixed Nat) String := blockCodec Prolly.LinkKey.mixed Encode.text
    let encode (block : Block Nat (Prolly.LinkKey.Mixed Nat) String) := (codec.encode? block).elim .invalidWire .found
    match name with
    | 1 => encode (.branch 1 [(obj, 2), (blob, 3)])
    | 2 => encode (.leaf [(obj, "object")])
    | 3 => encode (.leaf [(blob, "raw")])
    | _ => .missing

#guard (((Table.empty).checkedRoot linked 3 2 1 [2, 3, 1]).map fun (table, root) =>
  (table.locate 7, table.arena.lookup linked 3 2 root obj, table.arena.lookup linked 3 2 root blob)) =
  .ok (none, .ok (some "object"), .ok (some "raw"))

end Silmaril.Formats.Dasl.Arena.Prolly.Localize.Examples
