module

public import Silmaril.Formats.Cbor.WellFormed.Defs

/-!
# CBOR values, deterministic heads and a definite-length codec

A representation-level CBOR data model, a definite-length encoder with shortest heads, and a
decoder that inverts it. This is the substrate for deterministic profiles such as DRISL
(`Silmaril.Formats.Cbor.Drisl`).

* `Value`: unsigned and negative integers (`nint n` is `-1 - n`), byte and text strings
  (as bytes; text validity is a profile's business), arrays, maps as *ordered* lists of
  pairs (order and duplicates are kept, so a profile can require sorted, distinct keys),
  tags, simple values, and floats as a width in bytes (2, 4 or 8) and the raw IEEE 754 bits.
  RFC 8949's generic data model (§2) identifies more items than this one: for example the
  same number as a half and as a double float, or a definite and an indefinite string with
  the same content. So this is a model of *encodings up to argument width*, not of the
  generic data model, and equality here is finer than data-model equality.
* `encodeHead mt n`: the preferred (shortest) head of RFC 8949 §4.2.1 for an argument
  `n < 2^64`.
* `encode`: definite lengths and shortest heads everywhere, maps in their list order,
  floats at their stored width.
* `decode`: reads one definite-length item with any argument width; `ai = 31` (indefinite
  lengths) and the reserved values fail. `Thms` proves `decode` inverts `encode` on
  `Encodable` values.
-/

@[expose] public section

namespace Silmaril.Formats.Cbor

/-- A CBOR value at the level of its definite-length encoding. -/
inductive Value where
  | uint (n : Nat)
  /-- The negative integer `-1 - n`. -/
  | nint (n : Nat)
  | bytes (b : List UInt8)
  /-- A text string, as its bytes (UTF-8 validity is not part of the model). -/
  | text (t : List UInt8)
  | array (items : List Value)
  /-- A map as an ordered list of key-value pairs. -/
  | map (entries : List (Value × Value))
  | tag (n : Nat) (content : Value)
  /-- A simple value `0..23` or `32..255` (20 false, 21 true, 22 null, 23 undefined). -/
  | simple (n : Nat)
  /-- A float of `width` bytes (2, 4 or 8) with these IEEE 754 bits. -/
  | float (width : Nat) (bits : Nat)
  deriving Repr

/-- `false`. -/
def Value.false : Value := .simple 20
/-- `true`. -/
def Value.true : Value := .simple 21
/-- `null`. -/
def Value.null : Value := .simple 22

/-- The `k` big-endian bytes of `n` (taken modulo `256 ^ k`). -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n / 256 ^ k) :: beBytes k n

/-- The shortest head of major type `mt` for the argument `n` (RFC 8949 §4.2.1). -/
def encodeHead (mt n : Nat) : List UInt8 :=
  if n < 24 then [UInt8.ofNat (32 * mt + n)]
  else if n < 2 ^ 8 then UInt8.ofNat (32 * mt + 24) :: beBytes 1 n
  else if n < 2 ^ 16 then UInt8.ofNat (32 * mt + 25) :: beBytes 2 n
  else if n < 2 ^ 32 then UInt8.ofNat (32 * mt + 26) :: beBytes 4 n
  else UInt8.ofNat (32 * mt + 27) :: beBytes 8 n

/-- The additional information of a float width. -/
def floatAi : Nat → Nat
  | 2 => 25
  | 4 => 26
  | _ => 27

mutual

/-- The deterministic definite-length encoding (maps in list order). -/
def Value.encode : Value → List UInt8
  | .uint n => encodeHead 0 n
  | .nint n => encodeHead 1 n
  | .bytes b => encodeHead 2 b.length ++ b
  | .text t => encodeHead 3 t.length ++ t
  | .array xs => encodeHead 4 xs.length ++ encodeList xs
  | .map kvs => encodeHead 5 kvs.length ++ encodeMap kvs
  | .tag n v => encodeHead 6 n ++ v.encode
  | .simple n => if n < 24 then [UInt8.ofNat (0xE0 + n)] else [0xF8, UInt8.ofNat n]
  | .float w bits => UInt8.ofNat (0xE0 + floatAi w) :: beBytes w bits

/-- The encodings of a list of items, concatenated. -/
def encodeList : List Value → List UInt8
  | [] => []
  | v :: vs => v.encode ++ encodeList vs

/-- The encodings of key-value pairs, concatenated. -/
def encodeMap : List (Value × Value) → List UInt8
  | [] => []
  | (k, v) :: kvs => k.encode ++ v.encode ++ encodeMap kvs

end

mutual

/-- Arguments fit in 64 bits, simple values are encodable, floats have width 2, 4 or 8 and
fitting bits. -/
def Value.Encodable : Value → Prop
  | .uint n | .nint n => n < 2 ^ 64
  | .bytes b | .text b => b.length < 2 ^ 64
  | .array xs => xs.length < 2 ^ 64 ∧ ListEncodable xs
  | .map kvs => kvs.length < 2 ^ 64 ∧ MapEncodable kvs
  | .tag n v => n < 2 ^ 64 ∧ v.Encodable
  | .simple n => n < 24 ∨ (32 ≤ n ∧ n < 256)
  | .float w bits => (w = 2 ∨ w = 4 ∨ w = 8) ∧ bits < 256 ^ w

/-- Every item is encodable. -/
def ListEncodable : List Value → Prop
  | [] => True
  | v :: vs => v.Encodable ∧ ListEncodable vs

/-- Every key and value is encodable. -/
def MapEncodable : List (Value × Value) → Prop
  | [] => True
  | (k, v) :: kvs => k.Encodable ∧ v.Encodable ∧ MapEncodable kvs

end

/-- The float width of an additional information value `25..27`. -/
def aiWidth : Nat → Nat
  | 25 => 2
  | 26 => 4
  | _ => 8

mutual

/-- Decode one definite-length item, with fuel. -/
def decodeItem : Nat → List UInt8 → Option (Value × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, b :: r =>
    let mt := b.toNat / 32
    let ai := b.toNat % 32
    if 28 ≤ ai then none
    else if mt = 7 then
      if ai < 24 then some (.simple ai, r)
      else (readArg ai r).bind fun ar =>
        if ai = 24 then (if 32 ≤ ar.1 then some (.simple ar.1, ar.2) else none)
        else some (.float (aiWidth ai) ar.1, ar.2)
    else (readArg ai r).bind fun ar =>
      if mt = 0 then some (.uint ar.1, ar.2)
      else if mt = 1 then some (.nint ar.1, ar.2)
      else if mt = 2 then
        (if ar.1 ≤ ar.2.length then some (.bytes (ar.2.take ar.1), ar.2.drop ar.1) else none)
      else if mt = 3 then
        (if ar.1 ≤ ar.2.length then some (.text (ar.2.take ar.1), ar.2.drop ar.1) else none)
      else if mt = 4 then (decodeList n ar.1 ar.2).map fun p => (.array p.1, p.2)
      else if mt = 5 then (decodeMap n ar.1 ar.2).map fun p => (.map p.1, p.2)
      else (decodeItem n ar.2).map fun p => (.tag ar.1 p.1, p.2)

/-- Decode `k` items. -/
def decodeList : Nat → Nat → List UInt8 → Option (List Value × List UInt8)
  | _, 0, w => some ([], w)
  | 0, _ + 1, _ => none
  | f + 1, k + 1, w => (decodeItem f w).bind fun p =>
      (decodeList f k p.2).map fun q => (p.1 :: q.1, q.2)

/-- Decode `k` key-value pairs. -/
def decodeMap : Nat → Nat → List UInt8 → Option (List (Value × Value) × List UInt8)
  | _, 0, w => some ([], w)
  | 0, _ + 1, _ => none
  | f + 1, k + 1, w => (decodeItem f w).bind fun p => (decodeItem f p.2).bind fun q =>
      (decodeMap f k q.2).map fun s => ((p.1, q.1) :: s.1, s.2)

end

/-- Decode a whole input as one definite-length item. -/
def decode (w : List UInt8) : Option Value :=
  match decodeItem (2 * w.length + 2) w with
  | some (v, []) => some v
  | _ => none

end Silmaril.Formats.Cbor

end
