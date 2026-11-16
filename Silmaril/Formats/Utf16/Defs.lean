module

public import Mathlib.Computability.Language
public import Silmaril.Formats.Bytes

/-!
# The languages of well-formed UTF-16 bytes

UTF-16 as defined in Chapter 3 of the Unicode Standard: the encoding form (§3.9) maps each
Unicode scalar value to one or two 16-bit code units, and the encoding schemes (§3.10) serialize
code units as bytes.

* **Code units.** `WellFormedUnits us`: the code-unit sequence `us` is well-formed UTF-16
  (§3.9): each code unit is either a non-surrogate `0000..D7FF`/`E000..FFFF`, or a high
  surrogate `D800..DBFF` immediately followed by a low surrogate `DC00..DFFF`. Unpaired or
  reversed surrogates are ill-formed. `encodeChar` is the encoding form on one scalar value; the
  well-formed sequences are exactly the encodings of strings of scalar values
  (`wellFormedUnits_iff_exists_chars`).
* **Byte order.** `Endian.big` writes a code unit most significant byte first (UTF-16BE),
  `Endian.little` least significant byte first (UTF-16LE). `language e` is the set of
  serializations of well-formed code-unit sequences in that byte order. Every member has even
  length; an odd trailing byte is ill-formed.
* **Byte-order mark, explicit-endian schemes.** In UTF-16BE and UTF-16LE an initial `FE FF` /
  `FF FE` is not a byte-order mark: it is the character `U+FEFF` ZERO WIDTH NO-BREAK SPACE, part
  of the text (§3.10, the UTF-16BE and UTF-16LE encoding schemes). So `language .big` contains `FE FF 00 41` as the two characters
  `U+FEFF U+0041`, and nothing is stripped.
* **Byte-order mark, the UTF-16 scheme.** The UTF-16 encoding scheme (§3.10) is either byte order,
  with an optional initial byte-order mark that is not part of the text; without one it is
  big-endian (§3.10; RFC 2781 §4.3 says such text "SHOULD be interpreted as being big-endian", and
this definition takes that reading). `schemeLanguage` reads the bytes that way: an input starting
  `FF FE` is the mark followed by a member of `language .little`; any other input is a member of
  `language .big`. (An initial `FE FF` is the big-endian mark; dropping it or keeping it as
  `U+FEFF` gives the same well-formedness, so this case needs no rule of its own.) So
  `FF FE 00 D8` is not in the scheme, although it is well-formed UTF-16BE (`U+FFFE U+00D8`):
  after the mark, `00 D8` is the lone little-endian surrogate `D800`.

References (`references.bib`): `unicode-15-ch03` (§3.9, §3.10), `rfc2781`.
Lemmas: `Silmaril.Formats.Utf16.Thms`.
-/

@[expose] public section

namespace Silmaril.Formats.Utf16

/-! ## Code units (§3.9) -/

/-- A high-surrogate code unit, `D800..DBFF`. -/
def IsHigh (u : UInt16) : Prop := 0xD800 ≤ u ∧ u ≤ 0xDBFF

/-- A low-surrogate code unit, `DC00..DFFF`. -/
def IsLow (u : UInt16) : Prop := 0xDC00 ≤ u ∧ u ≤ 0xDFFF

/-- A surrogate code unit, `D800..DFFF`. -/
def IsSurrogate (u : UInt16) : Prop := 0xD800 ≤ u ∧ u ≤ 0xDFFF

instance (u : UInt16) : Decidable (IsHigh u) := by unfold IsHigh; infer_instance
instance (u : UInt16) : Decidable (IsLow u) := by unfold IsLow; infer_instance
instance (u : UInt16) : Decidable (IsSurrogate u) := by unfold IsSurrogate; infer_instance

/-- Well-formed UTF-16 code-unit sequences: non-surrogates, and high surrogates each
immediately followed by a low surrogate. -/
inductive WellFormedUnits : List UInt16 → Prop
  | nil : WellFormedUnits []
  /-- A code unit that is not a surrogate encodes the scalar value it equals. -/
  | single {u us} : ¬ IsSurrogate u → WellFormedUnits us → WellFormedUnits (u :: us)
  /-- A surrogate pair. -/
  | pair {hi lo us} : IsHigh hi → IsLow lo → WellFormedUnits us →
      WellFormedUnits (hi :: lo :: us)

/-- The UTF-16 encoding form of one scalar value (§3.9): itself below `U+10000`, otherwise the
surrogate pair `D800 + (v - 10000) / 400`, `DC00 + (v - 10000) % 400` (hexadecimal). -/
def encodeChar (c : Char) : List UInt16 :=
  if c.toNat < 0x10000 then [UInt16.ofNat c.toNat]
  else [UInt16.ofNat (0xD800 + (c.toNat - 0x10000) / 0x400),
    UInt16.ofNat (0xDC00 + (c.toNat - 0x10000) % 0x400)]

/-- The UTF-16 encoding form of a string of scalar values. -/
def encodeUnits (cs : List Char) : List UInt16 := cs.flatMap encodeChar

/-! ## Byte order (§3.10, the UTF-16BE and UTF-16LE encoding schemes) -/

/-- The byte order of an explicit-endian encoding scheme. -/
inductive Endian where
  /-- Most significant byte first: UTF-16BE. -/
  | big
  /-- Least significant byte first: UTF-16LE. -/
  | little
  deriving DecidableEq, Repr

/-- The two bytes of a code unit, in the given byte order. -/
def unitBytes : Endian → UInt16 → List UInt8
  | .big, u => [UInt8.ofNat (u.toNat / 0x100), UInt8.ofNat (u.toNat % 0x100)]
  | .little, u => [UInt8.ofNat (u.toNat % 0x100), UInt8.ofNat (u.toNat / 0x100)]

/-- The bytes of a code-unit sequence, in the given byte order. -/
def serialize (e : Endian) (us : List UInt16) : List UInt8 := us.flatMap (unitBytes e)

/-- The language of well-formed UTF-16BE (`.big`) or UTF-16LE (`.little`) byte sequences: the
serializations of well-formed code-unit sequences. -/
def language (e : Endian) : Language UInt8 :=
  {w | ∃ us, WellFormedUnits us ∧ w = serialize e us}

/-- The UTF-16 encoding scheme (§3.10, RFC 2781 §4.3): the mark `FF FE` followed by little-endian
text, or big-endian text not starting with `FF FE`. -/
def schemeLanguage : Language UInt8 :=
  {w | (∃ t ∈ language .little, w = [0xFF, 0xFE] ++ t) ∨
    (w ∈ language .big ∧ w.take 2 ≠ [0xFF, 0xFE])}

/-! ## Executable checks -/

/-- Read a byte sequence as code units in the given byte order; `none` on odd length. -/
def units (e : Endian) : List UInt8 → Option (List UInt16)
  | [] => some []
  | [_] => none
  | a :: b :: t =>
    let u := match e with
      | .big => UInt16.ofNat (a.toNat * 0x100 + b.toNat)
      | .little => UInt16.ofNat (b.toNat * 0x100 + a.toNat)
    (units e t).map (u :: ·)

/-- Check that a code-unit sequence is well-formed. -/
def wellFormedUnitsB : List UInt16 → Bool
  | [] => true
  | [u] => !decide (IsSurrogate u)
  | u :: v :: us =>
    if decide (IsHigh u) then decide (IsLow v) && wellFormedUnitsB us
    else !decide (IsSurrogate u) && wellFormedUnitsB (v :: us)

/-- Check membership in `language e`. -/
def isWellFormed (e : Endian) (w : List UInt8) : Bool :=
  match units e w with
  | some us => wellFormedUnitsB us
  | none => false

end Silmaril.Formats.Utf16

end
