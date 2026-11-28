module

import Silmaril.Formats.Csv.Typed.Codecs.Thms
meta import Silmaril.Formats.Csv.Typed.Codecs.Defs

/-! Executable controls for the codecs and their tagged CSV spelling. -/

open Silmaril.Formats.Csv (Field)
open Silmaril.Formats.Csv.Typed
open Silmaril.Formats.Csv.Typed.Codecs

private meta def bytes (s : String) : Field := s.toByteArray.data.toList

#guard int32.print Int32.minValue = some (bytes "-2147483648")
#guard int32.print Int32.maxValue = some (bytes "2147483647")
#guard int32.parse (bytes "-2147483648") = some Int32.minValue
#guard int32.parse (bytes "2147483647") = some Int32.maxValue
#guard int32.parse (bytes "0") = some 0
#guard int32.parse (bytes "-1") = some (-1)
#guard int32.parse (bytes "-2147483649") = none
#guard int32.parse (bytes "2147483648") = none
#guard int32.parse (bytes "000000000001") = none
#guard int32.parse (bytes "-0") = none
#guard int32.parse (bytes "01") = none
#guard int32.parse (bytes "-01") = none
#guard int32.parse (bytes "+1") = none
#guard int32.parse (bytes " 1") = none
#guard int32.parse (bytes "1\r\n") = none
#guard int32.parse (bytes "1.0") = none
#guard int32.parse (bytes "1e0") = none
#guard int32.parse (bytes "１") = none
#guard int32.parse (bytes "-") = none
#guard int32.parse [] = none

#guard utf8.print "" = some []
#guard utf8.parse [] = some ""
#guard utf8.print " a,\"b\"\r\nc\n " = some (bytes " a,\"b\"\r\nc\n ")
#guard utf8.parse (bytes " a,\"b\"\r\nc\n ") = some " a,\"b\"\r\nc\n "
#guard utf8.print "é" = none
#guard utf8.parse (bytes "é") = none
#guard utf8.print "a\tb" = none
#guard utf8.parse [0x00] = none
#guard utf8.parse [0x7F] = none
#guard utf8.parse [0xFF] = none

private meta def numberSchema : Schema Unit := ⟨1, fun _ => (bytes "number", ())⟩
private meta def textSchema : Schema Unit := ⟨1, fun _ => (bytes "text", ())⟩

#guard encode numberSchema (fun _ => int32) [fun _ => some Int32.minValue, fun _ => none] =
  .ok (bytes "\"number\"\r\n\"T-2147483648\"\r\n\"N\"\r\n")
#guard encode textSchema (fun _ => utf8) [fun _ => some "", fun _ => none, fun _ => some "a\"\nb"] =
  .ok (bytes "\"text\"\r\n\"T\"\r\n\"N\"\r\n\"Ta\"\"\nb\"\r\n")
#guard (decode numberSchema (fun _ => int32) (bytes "number\r\nT01")).map List.length =
  .error (.parseCell 0)
