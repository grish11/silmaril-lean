module

import Silmaril.Formats.Dasl.ShortKeySet.Thms
import Silmaril.Formats.Dasl.Wire.Defs
meta import Silmaril.Formats.Dasl.ShortKeySet.Thms
meta import Silmaril.Formats.Dasl.Wire.Defs

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.ShortKeySet
open Silmaril.Semantics (OrderedSet)

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def expect {Value : Type} (option : Option Value) (label : String) : IO Value :=
  match option with
  | some value => pure value
  | none => throw (IO.userError label)

private def byteTests : IO Unit := do
  let empty ← expect (Bytes.ofBytes? 2 []) "empty byte key"
  let initial ← expect (Bytes.ofBytes? 2 [0]) "prefix byte key"
  let longer ← expect (Bytes.ofBytes? 2 [0, 255]) "two byte key"
  let high ← expect (Bytes.ofBytes? 2 [255]) "high byte key"
  let layout := normalize [longer, high, empty, initial, longer]
  let expected := [empty, initial, longer, high]
  check (decide (layout.keys = expected) && cardinality layout == 4 && contains layout longer) "canonical byte set"
  let packed : Encode.TotalCodec (OrderedSet (Bytes 2)) (Shallow Nat) := packedBytesCodec
  let array : Encode.TotalCodec (OrderedSet (Bytes 2)) (Shallow Nat) := byteArrayCodec
  let bytes : Shallow Nat := .bytes ⟨#[0, 1, 0, 2, 0, 255, 1, 255]⟩
  match packed.encode layout with
  | .bytes actual => check (actual == ⟨#[0, 1, 0, 2, 0, 255, 1, 255]⟩) "packed byte lengths and contents"
  | _ => throw (IO.userError "expected a packed byte string")
  check (decide ((packed.decode? bytes).map (·.keys) = some expected)) "packed recovery"
  check (decide ((array.decode? (array.encode layout)).map (·.keys) = some expected)) "array recovery"
  check ((packed.decode? (array.encode layout)).isNone && (array.decode? bytes).isNone) "layouts stay distinct"
  check ((packed.decode? (.bytes ⟨#[2, 0]⟩)).isNone) "truncated key rejected"
  check ((packed.decode? (.bytes ⟨#[3, 0, 0, 0]⟩)).isNone) "key over the profile limit rejected"
  check ((packed.decode? (.bytes ⟨#[0, 0]⟩)).isNone) "duplicate empty key rejected"
  check ((packed.decode? (.bytes ⟨#[1, 0xff, 0]⟩)).isNone) "descending byte keys rejected"
  let longest ← expect (Bytes.ofBytes? 255 (List.replicate 255 255)) "maximum key length"
  let framed := pack [longest]
  check (framed.head? == some 255 && framed.length == 256) "maximum length does not wrap"
  check (decide (unpack 255 framed.length framed = some [longest])) "maximum length recovers"
  check ((Bytes.ofBytes? 255 (List.replicate 256 0)).isNone) "256-byte key exceeds every limit"

private def textTests : IO Unit := do
  let compos := "é"
  let decomp := String.ofList ['e', Char.ofNat 0x301]
  let composed ← expect (Text.ofString? 3 compos) "composed UTF-8 key"
  let decomposed ← expect (Text.ofString? 3 decomp) "decomposed UTF-8 key"
  check ((Text.ofString? 2 compos).isSome && (Text.ofString? 2 decomp).isNone) "count UTF-8 bytes, not characters"
  let layout := normalize [composed, decomposed, composed]
  let expected := [decomposed, composed]
  let packed : Encode.TotalCodec (OrderedSet (Text 3)) (Shallow Wire.Cid) := packedTextCodec
  let array : Encode.TotalCodec (OrderedSet (Text 3)) (Shallow Wire.Cid) := textArrayCodec
  check (cardinality layout == 2) "no Unicode normalization"
  check (decide ((array.decode? (array.encode layout)).map (·.keys) = some expected)) "text array recovery"
  check ((packed.decode? (.bytes ⟨#[2, 0xc0, 0x80]⟩)).isNone) "overlong UTF-8 rejected"
  check ((packed.decode? (.bytes ⟨#[1, 0xc3]⟩)).isNone) "incomplete UTF-8 rejected"
  let golden : ByteArray := ⟨#[0x47, 3, 0x65, 0xcc, 0x81, 2, 0xc3, 0xa9]⟩
  check (Wire.render? (packed.encode layout) == some golden) "packed UTF-8 golden wire bytes"
  check (decide (((Wire.parse? golden).bind packed.decode?).map (·.keys) = some expected)) "UTF-8 wire recovery"

public def main : IO Unit := do
  byteTests
  textTests
