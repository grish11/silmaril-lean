module

import Silmaril.Formats.Csv.Typed.Utf8.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Thms
meta import Silmaril.Formats.Csv.Typed.Utf8.Defs
meta import Silmaril.Formats.Csv.Typed.Codecs.Defs

/-! Regressions for typed UTF-8 wire admission and nullable tagging. -/

open Silmaril.Formats.Csv (Bytes Field)
open Silmaril.Formats.Csv.Typed (CellCodec Schema Table)
open Silmaril.Formats.Csv.Typed.Utf8 (encode decode string)

private def bytes (text : String) : Field := text.toUTF8.data.toList

private inductive Kind where
  | text
  | int32

private def Value : Kind → Type
  | .text => String
  | .int32 => Int32

private def schema : Schema Kind :=
  ⟨2, Fin.cases (bytes "名前", .text) (fun _ => (bytes "i32", .int32))⟩

private def codecs : (k : Kind) → CellCodec (Value k)
  | .text => string
  | .int32 => Silmaril.Formats.Csv.Typed.Codecs.int32

private def row (label : Option String) (number : Option Int32) :
    Silmaril.Relational.Scan.Row schema Value := Fin.cases label (fun _ => number)

private def observe (table : Table schema Value) : List (Option String × Option Int32) :=
  table.map fun item => (item (0 : Fin 2), item (1 : Fin 2))

private def data : Table schema Value :=
  [row none (some Int32.minValue), row (some "") none,
    row (some "N") (some 0), row (some "é,界\"🙂\r\n") (some Int32.maxValue)]

private def wire : Bytes := bytes <|
  "\"名前\",\"i32\"\r\n\"N\",\"T-2147483648\"\r\n\"T\",\"N\"\r\n\"TN\",\"T0\"\r\n" ++
    "\"Té,界\"\"🙂\r\n\",\"T2147483647\"\r\n"

#guard encode schema codecs data = .ok wire
#guard (decode schema codecs wire).map observe = .ok (observe data)
#guard (decode schema codecs (bytes "名前,i32\r\nT漢,T-1")).map observe = .ok [(some "漢", some (-1))]
#guard (decode schema codecs (bytes "名前,i32")).map observe = .ok []
#guard (decode schema codecs []).map observe = .error .missingHeader
#guard (decode schema codecs (bytes "i32,名前\r\nN,N")).map observe = .error .headerMismatch
#guard (decode schema codecs (bytes "名前,i32\r\nN")).map observe = .error (.width 2 1)
#guard (decode schema codecs (bytes "名前,i32\r\nN,N,N")).map observe = .error (.width 2 3)
#guard (decode schema codecs (bytes "名前,i32\r\n,N")).map observe = .error (.invalidTag 0)
#guard (decode schema codecs (bytes "名前,i32\r\nN,")).map observe = .error (.invalidTag 1)
#guard (decode schema codecs (bytes "名前,i32\r\nNé,N")).map observe = .error (.invalidTag 0)
#guard (decode schema codecs (bytes "名前,i32\r\nTé,T")).map observe = .error (.parseCell 1)
#guard (decode schema codecs (bytes "名前,i32\r\nN,T2147483648")).map observe = .error (.parseCell 1)
#guard (decode schema codecs (bytes "名前,i32\r\nN,T-2147483649")).map observe = .error (.parseCell 1)
#guard (decode schema codecs (bytes "名前,i32\r\nN,T+1")).map observe = .error (.parseCell 1)
#guard (decode schema codecs (bytes "名前,i32\r\nN,T01")).map observe = .error (.parseCell 1)
#guard (decode schema codecs (bytes "名前,i32\nN,N")).map observe = .error .malformedWire
#guard (decode schema codecs (bytes "名前,i32\r\nT" ++ [0xC0, 0xAF] ++ bytes ",N")).map observe =
  .error .malformedWire
#guard (decode schema codecs (bytes "名前,i32\r\n\"Té\t\",N")).map observe = .error .malformedWire

-- Valid UTF-8 text can still be outside the wire alphabet.
#guard string.print "é\t" = some (bytes "é\t")
#guard string.parse (bytes "é\t") = some "é\t"
#guard string.parse [0xED, 0xA0, 0x80] = none
#guard encode schema codecs [row (some "é\t") none] = .error .unrepresentableWire
#guard encode schema codecs [row (some (String.singleton (Char.ofNat 0))) none] =
  .error .unrepresentableWire
#guard Silmaril.Formats.Csv.Typed.encode schema codecs data = .error .unrepresentableWire

private def zero : Schema Kind := ⟨0, fun i => i.elim0⟩
private def zeroRows : Table zero Value := [fun i => i.elim0, fun i => i.elim0]

#guard encode zero codecs zeroRows = .ok (bytes "\"\"\r\n\"\"\r\n\"\"\r\n")
#guard (decode zero codecs (bytes "\"\"\r\n\"\"\r\n\"\"\r\n")).map List.length = .ok 2
#guard (decode zero codecs (bytes "\"\"\r\nN")).map List.length = .error .zeroColumnMarker
#guard encode zero codecs zeroRows = Silmaril.Formats.Csv.Typed.encode zero codecs zeroRows

example {table : Table schema Value} {output : Bytes} (h : encode schema codecs table = .ok output) :
    decode schema codecs output = .ok table :=
  Silmaril.Formats.Csv.Typed.Utf8.decode_encode
    (fun k => match k with
      | .text => Silmaril.Formats.Csv.Typed.Utf8.string_parsePrint
      | .int32 => Silmaril.Formats.Csv.Typed.Codecs.int32_parsePrint) h

example {table : Table schema Value} {input : Bytes} (h : decode schema codecs input = .ok table) :
    ∃ output, encode schema codecs table = .ok output ∧
      Silmaril.Formats.Csv.Utf8.decode output = Silmaril.Formats.Csv.Utf8.decode input :=
  Silmaril.Formats.Csv.Typed.Utf8.encode_of_decode
    (fun k => match k with
      | .text => Silmaril.Formats.Csv.Typed.Utf8.string_printParse
      | .int32 => Silmaril.Formats.Csv.Typed.Codecs.int32_printParse) h
