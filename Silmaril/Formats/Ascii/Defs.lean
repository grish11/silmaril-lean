module

public import Silmaril.Formats.JsonBytes.Defs

/-!
# The language of ASCII bytes

The byte sequences in which every byte is an ASCII code, `00..7F`, as a Mathlib
`Language UInt8`. ASCII is the 7-bit code that RFC 20 adopts for network interchange (USAS
X3.4-1968; its revision ANSI X3.4-1986 assigns the same 128 codes), sent as one byte per code
with the high bit clear. A byte `80..FF` is not ASCII, whatever an 8-bit extension (Latin-1,
Windows-1252, …) would make of it.

* `language`: every byte is `00..7F`. It contains control codes (`00..1F`, `7F`); the printable
  subset is `printable` (`20..7E`, the graphic characters and space).
* As text, ASCII bytes are UTF-8 (`language_le_utf8`): the one-byte rows of Unicode Table 3-7 are
  exactly the ASCII codes. Its members are exactly the UTF-8 encodings of the strings of
  characters `U+0000..U+007F` (`mem_language_iff_exists_chars`).
* `json p`: the JSON texts (`Silmaril.Formats.JsonBytes.language p`) written in ASCII only, so
  every non-ASCII character of a string is a `\u` escape. It is the intersection, not a new
  grammar, and is contained in the JSON language (`json_le`) and in `language`.

References (`references.bib`): `rfc20`, `unicode-15-ch03` (Table 3-7), `rfc8259`.
Lemmas: `Silmaril.Formats.Ascii.Thms`.
-/

@[expose] public section

namespace Silmaril.Formats.Ascii

/-- A byte is an ASCII code: its high bit is clear. -/
def IsAsciiByte (b : UInt8) : Prop := b < 0x80

instance (b : UInt8) : Decidable (IsAsciiByte b) := by unfold IsAsciiByte; infer_instance

/-- A byte is a printable ASCII character: space or a graphic character, `20..7E`. -/
def IsPrintableByte (b : UInt8) : Prop := 0x20 ≤ b ∧ b ≤ 0x7E

instance (b : UInt8) : Decidable (IsPrintableByte b) := by unfold IsPrintableByte; infer_instance

/-- The language of ASCII byte sequences: every byte is `00..7F`. -/
def language : Language UInt8 := {w | ∀ b ∈ w, IsAsciiByte b}

/-- The language of printable ASCII byte sequences: every byte is `20..7E`. -/
def printable : Language UInt8 := {w | ∀ b ∈ w, IsPrintableByte b}

/-- The executable check: every byte is below `0x80`. -/
def isAscii (w : List UInt8) : Bool := w.all (· < 0x80)

/-- JSON texts (RFC 8259, under the escape profile `p`) written in ASCII only. -/
def json (p : JsonBytes.Profile) : Language UInt8 := JsonBytes.language p ⊓ language

end Silmaril.Formats.Ascii

namespace Silmaril.Formats.Bytes

/-- A byte string is ASCII (`Silmaril.Formats.Ascii.language` on its list view). -/
def IsAscii (bytes : Bytes) : Prop := bytes.toList ∈ Ascii.language

end Silmaril.Formats.Bytes

end
