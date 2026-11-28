module

import Silmaril.Formats.Csv.Thms
meta import Silmaril.Formats.Csv.Defs

/-! Executable wire controls for the RFC 4180 grammar and profile decisions. -/

open Silmaril.Formats.Csv

private meta def bytes (s : String) : Bytes := s.toUTF8.data.toList

-- Quoted separators, doubled quotes, and line breaks inside quotes.
#guard decode (bytes "\"aaa\",\"b\"\"bb\",\"ccc\"") = some [[bytes "aaa", bytes "b\"bb", bytes "ccc"]]
#guard decode (bytes "\"a,b\",\"line 1\r\nline 2\"\r\n") = some [[bytes "a,b", bytes "line 1\r\nline 2"]]
#guard decode (bytes "\"a\rb\",\"c\nd\"") = some [[bytes "a\rb", bytes "c\nd"]]
#guard decode (bytes "\"\"\"\"") = some [[bytes "\""]]
#guard decode (bytes " a , b ") = some [[bytes " a ", bytes " b "]]

-- CRLF framing, including the final terminator and an intervening empty record.
#guard decode (bytes "a\r\n\r\nb") = some [[bytes "a"], [[]], [bytes "b"]]
#guard decode (bytes "a\r\nb\r\n") = decode (bytes "a\r\nb")
#guard decode (bytes "a\nb") = none
#guard decode (bytes "a\rb") = none
#guard decode (bytes "a\r") = none

-- Empty file, empty record field, and missing columns in ragged rows.
#guard decode [] = some []
#guard decode (bytes "\"\"") = some [[[]]]
#guard decode (bytes "\r\n") = some [[[]]]
#guard decode (bytes "a,b,c\r\nd,e\r\nf,g,\r\n") =
  some [[bytes "a", bytes "b", bytes "c"], [bytes "d", bytes "e"], [bytes "f", bytes "g", []]]
#guard decode (bytes ",") = some [[[], []]]

-- Malformed quoting, trailing junk, and bytes outside the ASCII profile.
#guard decode (bytes "a\"b") = none
#guard decode (bytes "\"a,b") = none
#guard decode (bytes "\"a\"x") = none
#guard decode (bytes "\"a\" ") = none
#guard decode (bytes "\"\"\"") = none
#guard decode (bytes "\"x\t\"") = none
#guard decode (bytes "é") = none
#guard decode [0xEF, 0xBB, 0xBF, 0x61] = none
#guard decode [0x61, 0x00] = none

-- Canonical emission uses quotes and CRLF and cannot emit a zero-field row.
#guard encode [] = some []
#guard encode [[[]]] = some (bytes "\"\"\r\n")
#guard encode [[bytes "a,b", bytes "b\"c", bytes "x\r\ny"]] =
  some (bytes "\"a,b\",\"b\"\"c\",\"x\r\ny\"\r\n")
#guard encode [[]] = none
#guard encode [[bytes "a\t"]] = none

example : decode [] = some [] := rfl

example : decode [0x22, 0x22] = some [[[]]] :=
  have record : Records [0x22, 0x22] [[]] [] :=
    .last (FieldWire.quoted (field := []) rfl)
  (decode_eq_some_iff _ _).mpr (.records (by decide) record)

example {rows : Rows} {wire : Bytes} (h : encode rows = some wire) : decode wire = some rows :=
  decode_encode h
