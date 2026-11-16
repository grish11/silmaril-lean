module

public import Mathlib.Computability.Language
public import Silmaril.Formats.Bytes

/-!
# Well-formed CBOR data items (RFC 8949)

The byte strings that are exactly one *well-formed* CBOR data item, in the sense of
RFC 8949 §1.2 and §3, as a `Language UInt8`. This is the syntactic layer only:

* **Well-formed** (this module): the item follows the syntax of §3. Its initial bytes,
  arguments, lengths and nesting are consistent, and nothing follows it.
* **Valid** (not here): well-formed and also obeying the semantics of §5.3. Text strings are
  UTF-8, maps have no duplicate keys, and tag contents meet each tag's own requirements. So,
  for example, a text string with ill-formed UTF-8, or a map with a repeated key, is well-formed
  but not valid.
* **Deterministically encoded** (not here): §4.2, preferred (shortest) arguments,
  definite lengths only, map keys in bytewise lexicographic order. Profiles such as
  CBOR/c or DRISL constrain it further.

## Well-formedness, explicitly

The inductive `Item` transcribes §3 and Appendix C:

* An initial byte has major type `mt = ib >> 5` and additional information `ai = ib & 0x1f`.
  `ai < 24` is the argument itself. `ai = 24, 25, 26, 27` take 1, 2, 4 or 8 following bytes,
  read big-endian, as the argument. `ai = 28..30` are reserved and never well-formed (§3).
  Arguments need not be in the shortest form (that is a determinism rule, §4.2.1), so `18 00`
  is a well-formed encoding of `0`.
* Major types 0 and 1 are integers. Major types 2 and 3 take as many content bytes as the
  argument; text content is not checked for UTF-8 (validity, §3.1). Major type 4 is followed by
  argument-many items, and major type 5 by twice that many (key, value, …). Major type 6 is
  followed by one item; any tag number is well-formed.
* Major type 7: `ai < 24` is a simple value. `ai = 24` takes one more byte, which must be at
  least 32 (§3.3: "not well-formed" otherwise). `ai = 25, 26, 27` are half-, single- and
  double-precision floats, with no constraint on their bits (NaN payloads, subnormals and
  negative zero are all well-formed).
* `ai = 31` is the indefinite length (§3.2). It is allowed only for major types 2 to 5. For
  major type 7 it is the "break" stop code, which is not a data item. It only ends an
  indefinite-length item: as an item of its own, inside a definite-length array or map, or
  in place of a map value, it makes the enclosing item not well-formed (§3.2.1, §3.2.2). The
  chunks of an indefinite-length string are definite-length strings of the same major type
  (§3.2.3).

A *single* data item is the whole input. A sequence of items (RFC 8742) is a separate
language, not defined here.

References (`references.bib`): `rfc8949`.
-/

@[expose] public section

namespace Silmaril.Formats.Cbor

/-- Big-endian (network byte order) value of a byte string. -/
def beNat (bytes : List UInt8) : Nat := bytes.foldl (fun a b => a * 256 + b.toNat) 0

/-- The number of argument bytes after the initial byte, for `ai = 24, 25, 26, 27`. -/
def argWidth : Nat → Option Nat
  | 24 => some 1
  | 25 => some 2
  | 26 => some 4
  | 27 => some 8
  | _ => none

/-- A head (initial byte and argument bytes) of major type `mt` whose argument is `arg`,
in any of its encodings. -/
def Head (mt arg : Nat) (w : List UInt8) : Prop :=
  (arg < 24 ∧ w = [UInt8.ofNat (32 * mt + arg)]) ∨
  ∃ ai k ext, argWidth ai = some k ∧ ext.length = k ∧ beNat ext = arg ∧
    w = UInt8.ofNat (32 * mt + ai) :: ext

/-- A definite-length string of major type `mt` (2 or 3): a head and argument-many bytes. -/
def DefiniteString (mt : Nat) (w : List UInt8) : Prop :=
  ∃ n h c, Head mt n h ∧ c.length = n ∧ w = h ++ c

/-- The chunks of an indefinite-length string: definite strings of the same major type. -/
def Chunks (mt : Nat) (w : List UInt8) : Prop :=
  ∃ parts : List (List UInt8), w = parts.flatten ∧ ∀ x ∈ parts, DefiniteString mt x

/-- The `break` stop code `FF`. -/
def breakByte : UInt8 := 0xFF

mutual

/-- One well-formed CBOR data item. -/
inductive Item : List UInt8 → Prop
  /-- Major type 0: an unsigned integer. -/
  | uint {n h} : Head 0 n h → Item h
  /-- Major type 1: a negative integer `-1 - n`. -/
  | nint {n h} : Head 1 n h → Item h
  /-- Major types 2 and 3: definite-length byte and text strings. -/
  | string {mt w} : (mt = 2 ∨ mt = 3) → DefiniteString mt w → Item w
  /-- Major types 2 and 3 with `ai = 31`: chunks, then `break`. -/
  | indefString {mt cs} : (mt = 2 ∨ mt = 3) → Chunks mt cs →
      Item (UInt8.ofNat (32 * mt + 31) :: cs ++ [breakByte])
  /-- Major type 4: `n` items. -/
  | array {n h xs} : Head 4 n h → Items n xs → Item (h ++ xs)
  /-- Major type 4 with `ai = 31`: items, then `break`. -/
  | indefArray {k xs} : Items k xs → Item (0x9F :: xs ++ [breakByte])
  /-- Major type 5: `n` key-value pairs. -/
  | map {n h xs} : Head 5 n h → Items (2 * n) xs → Item (h ++ xs)
  /-- Major type 5 with `ai = 31`: pairs, then `break`. -/
  | indefMap {k xs} : Items (2 * k) xs → Item (0xBF :: xs ++ [breakByte])
  /-- Major type 6: a tag number and one item. -/
  | tag {n h x} : Head 6 n h → Item x → Item (h ++ x)
  /-- Major type 7, `ai < 24`: a simple value (20 to 23 are false, true, null, undefined). -/
  | simple {v : Nat} : v < 24 → Item [UInt8.ofNat (0xE0 + v)]
  /-- Major type 7, `ai = 24`: a simple value of at least 32 in the next byte. -/
  | simpleByte {v : UInt8} : 32 ≤ v.toNat → Item [0xF8, v]
  /-- Major type 7, `ai = 25, 26, 27`: a float of 2, 4 or 8 bytes. -/
  | float {ai k e} : argWidth ai = some k → 25 ≤ ai → e.length = k →
      Item (UInt8.ofNat (0xE0 + ai) :: e)

/-- `n` consecutive items. -/
inductive Items : Nat → List UInt8 → Prop
  | nil : Items 0 []
  | cons {n x xs} : Item x → Items n xs → Items (n + 1) (x ++ xs)

end

/-- The byte strings that are exactly one well-formed CBOR data item. -/
def wellFormed : Language UInt8 := {w | Item w}

/-! ## A decision procedure (RFC 8949 Appendix C, with fuel) -/

/-- The argument for additional information `ai < 28`, and the remaining bytes. -/
def readArg (ai : Nat) (r : List UInt8) : Option (Nat × List UInt8) :=
  if ai < 24 then some (ai, r)
  else match argWidth ai with
    | some k => if k ≤ r.length then some (beNat (r.take k), r.drop k) else none
    | none => none

mutual

/-- Skip one item; the bytes after it. -/
def skip : Nat → List UInt8 → Option (List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, b :: r =>
    let mt := b.toNat / 32
    let ai := b.toNat % 32
    if ai = 31 then
      if mt = 2 ∨ mt = 3 then skipChunks n mt r
      else if mt = 4 then skipUntilBreak n r
      else if mt = 5 then skipPairsUntilBreak n r
      else none
    else if mt = 7 then
      if ai < 24 then some r
      else if ai = 24 then
        match r with
        | v :: r' => if 32 ≤ v.toNat then some r' else none
        | [] => none
      else (readArg ai r).map Prod.snd
    else
      (readArg ai r).bind fun ar =>
        if mt = 0 ∨ mt = 1 then some ar.2
        else if mt = 2 ∨ mt = 3 then (if ar.1 ≤ ar.2.length then some (ar.2.drop ar.1) else none)
        else if mt = 4 then skipN n ar.1 ar.2
        else if mt = 5 then skipN n (2 * ar.1) ar.2
        else skip n ar.2

/-- Skip `k` items. -/
def skipN : Nat → Nat → List UInt8 → Option (List UInt8)
  | _, 0, w => some w
  | 0, _ + 1, _ => none
  | f + 1, k + 1, w => (skip f w).bind (skipN f k)

/-- Skip items up to and including `break`. -/
def skipUntilBreak : Nat → List UInt8 → Option (List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, b :: r =>
    if b = breakByte then some r else (skip f (b :: r)).bind (skipUntilBreak f)

/-- Skip key-value pairs up to and including `break`. -/
def skipPairsUntilBreak : Nat → List UInt8 → Option (List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, b :: r =>
    if b = breakByte then some r
    else (skip f (b :: r)).bind fun r1 => (skip f r1).bind (skipPairsUntilBreak f)

/-- Skip definite-length chunks of major type `mt` up to and including `break`. -/
def skipChunks : Nat → Nat → List UInt8 → Option (List UInt8)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | f + 1, mt, b :: r =>
    if b = breakByte then some r
    else if b.toNat / 32 = mt ∧ b.toNat % 32 < 28 then
      (readArg (b.toNat % 32) r).bind fun ar =>
        if ar.1 ≤ ar.2.length then skipChunks f mt (ar.2.drop ar.1) else none
    else none

end

/-- Decide well-formedness: one item, then nothing. -/
def isWellFormed (w : List UInt8) : Bool := skip (2 * w.length + 1) w == some []

end Silmaril.Formats.Cbor

end
