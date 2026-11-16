module

public import Silmaril.Formats.Utf8.Defs

/-!
# The language of valid JSON texts, over bytes

The byte sequences that are a JSON text (RFC 8259) encoded in UTF-8, as a Mathlib
`Language UInt8`. This is a specification, not a parser: it fixes which inputs are valid, and
is meant to be what readers such as `Silmaril.Formats.JsonWire.parse?` are checked against. No
theorem here relates the language to any reader.

## The standard and the choices made explicit

* **Grammar.** The ABNF of RFC 8259 §2–§7, transcribed rule for rule: `JSON-text = ws value
  ws`; `value`; `object`, `member`, `array` with the structural tokens `begin-array = ws %x5B
  ws` and so on; `number`; `string`. Its lexical rules are Mathlib `RegularExpression UInt8`s,
  and the nesting rules are the inductive predicates `Value`, `Elements`, `Members`.
* **Encoding.** RFC 8259 §8.1 requires UTF-8 for JSON exchanged between systems. Over bytes, the
  `unescaped` characters `%x20-21 / %x23-5B / %x5D-10FFFF` are the ASCII bytes `20-21 23-5B
  5D-7F` and the well-formed multi-byte sequences of Unicode Table 3-7 (`Utf8.multibyte`). So
  overlong forms, encoded surrogates (`ED A0..BF ..`), bytes `C0 C1 F5..FF`, stray continuation
  bytes and truncated sequences are rejected. Outside strings, only ASCII bytes occur.
* **Byte-order mark.** RFC 8259 §8.1 says implementations "MUST NOT add a byte order mark",
  though parsers "MAY ignore" one. The language does not contain BOM-prefixed texts: a reader
  that skips a BOM accepts more than this language.
* **Whitespace.** Exactly the four bytes `20 09 0A 0D` (§2). No other Unicode space, no
  comments.
* **Complete input.** A text is the whole input: `ws value ws` with nothing before or after.
  Prefixes of valid texts (`[1`), several values (`1 2`) and trailing garbage are not texts. The
  top level may be any value, including a scalar (§2, as in RFC 7159 and later).
* **Numbers.** `[ minus ] int [ frac ] [ exp ]` with `int = zero / ( digit1-9 *DIGIT )` (§6): no
  leading zeros, no `+` sign before the integer, no bare `.5` or `5.`, no `Infinity`/`NaN`, no
  hexadecimal. The language has no precision or range limits.
* **Escapes and surrogates.** RFC 8259 §7 allows any `\uXXXX`, including lone or reversed
  surrogate escapes. §8.2 calls such strings syntactically valid with unpredictable
  behaviour. The `Profile` makes the choice explicit:
  - `Profile.rfc8259`: the RFC grammar, any four hex digits.
  - `Profile.scalarEscapes`: every escape sequence denotes a Unicode scalar value. A
    `\uD800-\uDBFF` escape must be immediately followed by a `\uDC00-\uDFFF` escape, and a
    `\uDC00-\uDFFF` escape occurs only there. Every string then denotes a sequence of scalar
    values. This is the string condition of I-JSON (RFC 7493 §2.1) restricted to surrogates. It
    does not also forbid noncharacters, duplicate names or imprecise numbers, as I-JSON does, so
    it is not I-JSON.
* **Duplicate names** are a matter of the data model (§4 "SHOULD be unique"). The grammar
  accepts them, as RFC 8259 does.

References (`references.bib`): `rfc8259`, `rfc7493`, `rfc3629`, `unicode-15-ch03`.
Lemmas: `Silmaril.Formats.JsonBytes.Thms`.
-/

@[expose] public section

namespace Silmaril.Formats.JsonBytes

open RegularExpression Silmaril.Formats.Utf8

/-- How `\u` escapes are constrained (see the module documentation). -/
inductive Profile where
  /-- RFC 8259 §7 exactly: any `\uXXXX`, lone surrogate escapes included. -/
  | rfc8259
  /-- Escapes denote Unicode scalar values: surrogate escapes only as high-low pairs. -/
  | scalarEscapes
  deriving DecidableEq, Repr

/-! ## Lexical rules (RFC 8259 §2, §6, §7) -/

/-- The four whitespace bytes: space, horizontal tab, line feed, carriage return. -/
def IsWsByte (b : UInt8) : Prop := b = 0x20 ∨ b = 0x09 ∨ b = 0x0A ∨ b = 0x0D

instance (b : UInt8) : Decidable (IsWsByte b) := by unfold IsWsByte; infer_instance

/-- The whitespace bytes as a regular expression. -/
def wsByte : RegularExpression UInt8 := anyOf [0x20, 0x09, 0x0A, 0x0D]

/-- `ws = *( %x20 / %x09 / %x0A / %x0D )`. -/
def ws : RegularExpression UInt8 := star wsByte

/-- A structural character with insignificant whitespace on both sides (§2). -/
def structural (b : UInt8) : RegularExpression UInt8 := ws * char b * ws

/-- `begin-array = ws %x5B ws` (`[`). -/
def beginArray : RegularExpression UInt8 := structural 0x5B
/-- `end-array = ws %x5D ws` (`]`). -/
def endArray : RegularExpression UInt8 := structural 0x5D
/-- `begin-object = ws %x7B ws` (`{`). -/
def beginObject : RegularExpression UInt8 := structural 0x7B
/-- `end-object = ws %x7D ws` (`}`). -/
def endObject : RegularExpression UInt8 := structural 0x7D
/-- `name-separator = ws %x3A ws` (`:`). -/
def nameSeparator : RegularExpression UInt8 := structural 0x3A
/-- `value-separator = ws %x2C ws` (`,`). -/
def valueSeparator : RegularExpression UInt8 := structural 0x2C

/-- `false = %x66.61.6c.73.65`. -/
def falseLit : RegularExpression UInt8 := word [0x66, 0x61, 0x6C, 0x73, 0x65]
/-- `null = %x6e.75.6c.6c`. -/
def nullLit : RegularExpression UInt8 := word [0x6E, 0x75, 0x6C, 0x6C]
/-- `true = %x74.72.75.65`. -/
def trueLit : RegularExpression UInt8 := word [0x74, 0x72, 0x75, 0x65]

/-- `DIGIT = %x30-39`. -/
def digit : RegularExpression UInt8 := byteRange 0x30 0x39
/-- `digit1-9 = %x31-39`. -/
def digit19 : RegularExpression UInt8 := byteRange 0x31 0x39
/-- `1*DIGIT`. -/
def digits : RegularExpression UInt8 := digit * star digit
/-- `int = zero / ( digit1-9 *DIGIT )`. -/
def int : RegularExpression UInt8 := char 0x30 + digit19 * star digit
/-- `frac = decimal-point 1*DIGIT`. -/
def frac : RegularExpression UInt8 := char 0x2E * digits
/-- `exp = e [ minus / plus ] 1*DIGIT`, with `e = %x65 / %x45`. -/
def exp : RegularExpression UInt8 := anyOf [0x65, 0x45] * (1 + anyOf [0x2D, 0x2B]) * digits
/-- `number = [ minus ] int [ frac ] [ exp ]`. -/
def number : RegularExpression UInt8 := (1 + char 0x2D) * int * (1 + frac) * (1 + exp)

/-- `HEXDIG`, in either case (RFC 5234 `HEXDIG` is case-insensitive in ABNF strings). -/
def hexdig : RegularExpression UInt8 := digit + byteRange 0x41 0x46 + byteRange 0x61 0x66

/-- `unescaped = %x20-21 / %x23-5B / %x5D-10FFFF`, UTF-8 encoded: the ASCII bytes other than
controls, `"` and `\`, or one well-formed multi-byte UTF-8 sequence. -/
def unescaped : RegularExpression UInt8 :=
  byteRange 0x20 0x21 + byteRange 0x23 0x5B + byteRange 0x5D 0x7F + multibyte

/-- The two-character escapes `\" \\ \/ \b \f \n \r \t`. -/
def shortEscape : RegularExpression UInt8 :=
  char 0x5C * anyOf [0x22, 0x5C, 0x2F, 0x62, 0x66, 0x6E, 0x72, 0x74]

/-- `\u` (`%x5C %x75`). -/
def uPrefix : RegularExpression UInt8 := char 0x5C * char 0x75

/-- Any `\uXXXX` escape (RFC 8259 §7). -/
def unitEscape : RegularExpression UInt8 := uPrefix * hexdig * hexdig * hexdig * hexdig

/-- `d` or `D`. -/
def hexD : RegularExpression UInt8 := anyOf [0x44, 0x64]

/-- A `\uXXXX` escape of a non-surrogate code point: first digit other than `d`, or `d`
followed by `0-7` (`U+0000..U+D7FF`, `U+E000..U+FFFF`). -/
def bmpEscape : RegularExpression UInt8 :=
  uPrefix * ((digit + anyOf [0x41, 0x42, 0x43, 0x45, 0x46, 0x61, 0x62, 0x63, 0x65, 0x66]) *
      hexdig * hexdig * hexdig +
    hexD * byteRange 0x30 0x37 * hexdig * hexdig)

/-- A high-surrogate escape `\uD800..\uDBFF`. -/
def highEscape : RegularExpression UInt8 :=
  uPrefix * hexD * anyOf [0x38, 0x39, 0x41, 0x42, 0x61, 0x62] * hexdig * hexdig

/-- A low-surrogate escape `\uDC00..\uDFFF`. -/
def lowEscape : RegularExpression UInt8 :=
  uPrefix * hexD * anyOf [0x43, 0x44, 0x45, 0x46, 0x63, 0x64, 0x65, 0x66] * hexdig * hexdig

/-- One `char` of a string (§7), under the escape profile. -/
def strChar : Profile → RegularExpression UInt8
  | .rfc8259 => unescaped + shortEscape + unitEscape
  | .scalarEscapes => unescaped + shortEscape + bmpEscape + highEscape * lowEscape

/-- `string = quotation-mark *char quotation-mark`. -/
def string (p : Profile) : RegularExpression UInt8 := char 0x22 * star (strChar p) * char 0x22

/-- The values without nested structure: `false`, `null`, `true`, numbers and strings. -/
def scalar (p : Profile) : RegularExpression UInt8 :=
  falseLit + nullLit + trueLit + number + string p

/-! ## Nesting rules (RFC 8259 §2–§5) -/

mutual

/-- `value = false / null / true / object / array / number / string`. -/
inductive Value (p : Profile) : List UInt8 → Prop
  | scalar {w} : w ∈ (scalar p).matches' → Value p w
  /-- `begin-array end-array`. -/
  | emptyArray {a b} : a ∈ beginArray.matches' → b ∈ endArray.matches' → Value p (a ++ b)
  /-- `begin-array value *( value-separator value ) end-array`. -/
  | array {a xs b} : a ∈ beginArray.matches' → Elements p xs → b ∈ endArray.matches' →
      Value p (a ++ xs ++ b)
  /-- `begin-object end-object`. -/
  | emptyObject {a b} : a ∈ beginObject.matches' → b ∈ endObject.matches' → Value p (a ++ b)
  /-- `begin-object member *( value-separator member ) end-object`. -/
  | object {a ms b} : a ∈ beginObject.matches' → Members p ms → b ∈ endObject.matches' →
      Value p (a ++ ms ++ b)

/-- `value *( value-separator value )`. -/
inductive Elements (p : Profile) : List UInt8 → Prop
  | one {v} : Value p v → Elements p v
  | cons {v s vs} : Value p v → s ∈ valueSeparator.matches' → Elements p vs →
      Elements p (v ++ s ++ vs)

/-- `member *( value-separator member )`, with `member = string name-separator value`. -/
inductive Members (p : Profile) : List UInt8 → Prop
  | one {k c v} : k ∈ (string p).matches' → c ∈ nameSeparator.matches' → Value p v →
      Members p (k ++ c ++ v)
  | cons {k c v s ms} : k ∈ (string p).matches' → c ∈ nameSeparator.matches' → Value p v →
      s ∈ valueSeparator.matches' → Members p ms → Members p (k ++ c ++ v ++ s ++ ms)

end

/-- `JSON-text = ws value ws`, the whole input. -/
def Text (p : Profile) (w : List UInt8) : Prop :=
  ∃ a v b, a ∈ ws.matches' ∧ Value p v ∧ b ∈ ws.matches' ∧ w = a ++ v ++ b

/-- The language of JSON texts over bytes, under an escape profile. -/
def language (p : Profile) : Language UInt8 := {w | Text p w}

end Silmaril.Formats.JsonBytes

namespace Silmaril.Formats.Bytes

/-- A byte string is one complete JSON text (`Silmaril.Formats.JsonBytes.language`). -/
def IsJson (p : JsonBytes.Profile) (bytes : Bytes) : Prop := bytes.toList ∈ JsonBytes.language p

end Silmaril.Formats.Bytes

end
