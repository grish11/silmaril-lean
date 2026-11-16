module

public import Mathlib.Computability.RegularExpressions
public import Silmaril.Formats.Bytes

/-!
# The language of well-formed UTF-8 bytes

The byte sequences that are well-formed UTF-8, as a Mathlib `Language UInt8`. The definition
transcribes Table 3-7 ("Well-Formed UTF-8 Byte Sequences") of the Unicode Standard, which is
also the grammar `UTF8-octets` of RFC 3629 §4. Every well-formed sequence is the encoding of a
sequence of Unicode scalar values, so the table excludes:

* overlong forms (`C0`, `C1`, `E0 80..9F`, `F0 80..8F` as lead bytes or second bytes),
* encoded surrogates `U+D800..U+DFFF` (`ED A0..BF`),
* code points above `U+10FFFF` (`F4 90..BF`, `F5..FF`),
* truncated sequences and stray continuation bytes.

A byte-order mark `EF BB BF` is the well-formed encoding of `U+FEFF`; this language does not
strip it (protocols such as JSON decide whether it is allowed).

The definitions are Mathlib `RegularExpression UInt8`s whose `matches'` are the languages.
Membership is decided by Mathlib's Brzozowski matcher `RegularExpression.rmatch`
(`RegularExpression.rmatch_iff_matches'`): `Silmaril.Formats.Utf8.Thms` gives the `Decidable`
instances, so closed examples are checked by `decide`.

References (`references.bib`): `unicode-15-ch03` (Table 3-7), `rfc3629` (§4).
Lemmas: `Silmaril.Formats.Utf8.Thms`.
-/

@[expose] public section

namespace Silmaril.Formats.Utf8

open RegularExpression

/-- Any one of the listed bytes. -/
def anyOf (bytes : List UInt8) : RegularExpression UInt8 :=
  bytes.foldr (fun b rest => char b + rest) 0

/-- The bytes `lo, lo + 1, …, hi`, in increasing order (empty if `hi < lo`). -/
def rangeList (lo hi : UInt8) : List UInt8 :=
  (List.range (hi.toNat + 1 - lo.toNat)).map fun i => UInt8.ofNat (lo.toNat + i)

/-- Any one byte `b` with `lo ≤ b ≤ hi`. -/
def byteRange (lo hi : UInt8) : RegularExpression UInt8 := anyOf (rangeList lo hi)

/-- The given bytes, in order. -/
def word (bytes : List UInt8) : RegularExpression UInt8 :=
  bytes.foldr (fun b rest => char b * rest) 1

/-- A continuation byte `80..BF`. -/
def tail : RegularExpression UInt8 := byteRange 0x80 0xBF

/-- One-byte sequences `00..7F`: the scalar values `U+0000..U+007F`. -/
def ascii : RegularExpression UInt8 := byteRange 0x00 0x7F

/-- Two-byte sequences (`U+0080..U+07FF`): `C2..DF 80..BF`. -/
def seq2 : RegularExpression UInt8 := byteRange 0xC2 0xDF * tail

/-- Three-byte sequences (`U+0800..U+FFFF` except the surrogates), the rows of Table 3-7:
`E0 A0..BF 80..BF`, `E1..EC 80..BF 80..BF`, `ED 80..9F 80..BF`, `EE..EF 80..BF 80..BF`. -/
def seq3 : RegularExpression UInt8 :=
  char 0xE0 * byteRange 0xA0 0xBF * tail +
  byteRange 0xE1 0xEC * tail * tail +
  char 0xED * byteRange 0x80 0x9F * tail +
  byteRange 0xEE 0xEF * tail * tail

/-- Four-byte sequences (`U+10000..U+10FFFF`), the rows of Table 3-7:
`F0 90..BF 80..BF 80..BF`, `F1..F3 80..BF 80..BF 80..BF`, `F4 80..8F 80..BF 80..BF`. -/
def seq4 : RegularExpression UInt8 :=
  char 0xF0 * byteRange 0x90 0xBF * tail * tail +
  byteRange 0xF1 0xF3 * tail * tail * tail +
  char 0xF4 * byteRange 0x80 0x8F * tail * tail

/-- The multi-byte encodings: one scalar value `U+0080..U+10FFFF`. -/
def multibyte : RegularExpression UInt8 := seq2 + seq3 + seq4

/-- The encoding of exactly one Unicode scalar value (Table 3-7, one row). -/
def scalar : RegularExpression UInt8 := ascii + multibyte

/-- Well-formed UTF-8: any finite concatenation of encoded scalar values (RFC 3629
`UTF8-octets = *( UTF8-char )`). -/
def wellFormed : RegularExpression UInt8 := star scalar

/-- The language of well-formed UTF-8 byte sequences. -/
def language : Language UInt8 := wellFormed.matches'

/-- A byte list is well-formed UTF-8. -/
def IsWellFormed (bytes : List UInt8) : Prop := bytes ∈ language

/-- The executable check: Mathlib's derivative matcher on `wellFormed`. -/
def isWellFormed (bytes : List UInt8) : Bool := wellFormed.rmatch bytes

end Silmaril.Formats.Utf8

namespace Silmaril.Formats.Bytes

/-- A byte string is well-formed UTF-8 (`Silmaril.Formats.Utf8.language` on its list view). -/
def IsUtf8 (bytes : Bytes) : Prop := Utf8.IsWellFormed bytes.toList

end Silmaril.Formats.Bytes

end
