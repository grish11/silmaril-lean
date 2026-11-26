module

import Silmaril.Formats.Csv.Utf8.Thms
meta import Silmaril.Formats.Csv.Utf8.Defs

/-! Executable controls for byte preservation, delimiter handling, and validation. -/

open Silmaril.Formats.Csv (Bytes)
open Silmaril.Formats.Csv.Utf8

private meta def bytes (s : String) : Bytes := s.toUTF8.data.toList

#guard decode (bytes "café,東京,🙂") = some [[bytes "café", bytes "東京", bytes "🙂"]]
#guard decode (bytes "\"а,б\",\"🙂\"\"é\",\"界\r\n字\",\"é\rà\",\"β\nγ\"\r\n") =
  some [[bytes "а,б", bytes "🙂\"é", bytes "界\r\n字", bytes "é\rà", bytes "β\nγ"]]
#guard decode (bytes "é,\r\n界\r\n") = some [[bytes "é", []], [bytes "界"]]
#guard encode [[bytes "café", bytes "東\"京", bytes "β\nγ"]] =
  some (bytes "\"café\",\"東\"\"京\",\"β\nγ\"\r\n")
#guard decode [0xEF, 0xBB, 0xBF, 0x61] = some [[[0xEF, 0xBB, 0xBF, 0x61]]]
#guard decode [0x65, 0xCC, 0x81] = some [[[0x65, 0xCC, 0x81]]]

#guard decode [] = some []
#guard decode (bytes "\"\"") = some [[[]]]
#guard decode (bytes "\r\n") = some [[[]]]
#guard encode [] = some []
#guard encode [[[]]] = some (bytes "\"\"\r\n")
#guard encode [[]] = none
#guard decode (bytes "é\nà") = none
#guard decode (bytes "é\r") = none
#guard decode (bytes "\"é\"x") = none
#guard decode (bytes "\"é\t\"") = none
#guard encode [[bytes "é\t"]] = none

-- UTF-8 must be well formed within a single unescaped field.
#guard decode [0x80] = none
#guard decode [0xC0, 0xAF] = none
#guard decode [0xED, 0xA0, 0x80] = none
#guard decode [0xF4, 0x90, 0x80, 0x80] = none
#guard decode [0xC3, 0x2C, 0xA9] = none
#guard decode [0x22, 0xE2, 0x82, 0x22] = none
#guard decode [0x22, 0xC3, 0x22, 0x22, 0xA9, 0x22] = none
#guard encode [[[0xC3], [0xA9]]] = none
#guard encode [[[0xED, 0xA0, 0x80]]] = none

#guard decode (bytes "\"a,b\",c\r\n") = Silmaril.Formats.Csv.decode (bytes "\"a,b\",c\r\n")
#guard decode (bytes "a\nb") = Silmaril.Formats.Csv.decode (bytes "a\nb")
#guard encode [[bytes "a,b", []]] = Silmaril.Formats.Csv.encode [[bytes "a,b", []]]
#guard Silmaril.Formats.Csv.decode (bytes "café") = none
