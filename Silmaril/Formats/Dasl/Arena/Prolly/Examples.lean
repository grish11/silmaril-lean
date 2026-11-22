module

import Silmaril.Formats.Dasl.Arena.Prolly.Thms
import Silmaril.Formats.Dasl.Prolly.LinkKey.Defs
public meta import Silmaril.Formats.Dasl.Arena.Prolly.Defs
public meta import Silmaril.Formats.Dasl.Prolly.LinkKey.Defs
public meta import Silmaril.Formats.Dasl.Prolly.Scan.Defs

namespace Silmaril.Formats.Dasl.Arena.Prolly.Examples

open Silmaril.Formats.Dasl.Prolly (blockCodec)

variable {Key : Type}

private def childBytes : ByteArray := ⟨#[2]⟩
private def rootBytes : ByteArray := ⟨#[1]⟩

private def byteFixture (codec : BlockCodec Nat Key String) (first last : Key) : RawStore.Decoder Nat where
  objectName := fun _ => True
  rawName := fun _ => False
  disjoint := fun {_} _ bot => bot
  parse? bytes := if bytes == rootBytes then codec.encode? (.branch 1 [(last, 2)])
    else if bytes == childBytes then codec.encode? (.leaf [(first, "found")]) else none

private def fetch : Nat → Option ByteArray
  | 1 => some rootBytes
  | 2 => some childBytes
  | 3 => some ⟨#[0]⟩
  | _ => none

private def ordinary : BlockCodec Nat String String := blockCodec Encode.text Encode.text

private def captured (codec : BlockCodec Nat Key String) (first last : Key) (names : List Nat) : Resident Nat Key String :=
  Resident.capture codec (@readRaw Nat (byteFixture codec first last) (fun _ => isTrue True.intro) fetch) names

#guard (captured ordinary "k" "k" [1, 2]).lookup 4 2 1 "k" = .ok (some "found")
#guard (captured ordinary "k" "k" [1, 2]).lookup 4 2 1 "a" = .ok none
#guard (captured ordinary "k" "k" [1]).lookup 4 2 1 "k" = .error (.missing 2)
#guard (captured ordinary "k" "k" [1, 2]).lookup 4 1 1 "k" = .error (.fuel 2)
#guard (captured ordinary "k" "k" [3]).lookup 4 2 3 "k" = .error (.invalidWire 3)

private def badNode : Resident Nat String String := Resident.capture ordinary (fun _ => .found .null) [1]
#guard badNode.lookup 4 2 1 "k" = .error (.invalidNode 1)

private def linked : BlockCodec Nat (Prolly.LinkKey.Mixed Nat) String := blockCodec Prolly.LinkKey.mixed Encode.text
private def key : Prolly.LinkKey.Mixed Nat := Prolly.LinkKey.tagged (.blob 7)
private def linkedResident : Resident Nat (Prolly.LinkKey.Mixed Nat) String := captured linked key key [1, 2]

#guard linkedResident.lookup 4 2 1 key = .ok (some "found")
#guard linkedResident.lookup 4 2 1 (Prolly.LinkKey.tagged (.obj 7)) = .ok none

end Silmaril.Formats.Dasl.Arena.Prolly.Examples
