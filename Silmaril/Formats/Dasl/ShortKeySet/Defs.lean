module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.String.Basic
public import Silmaril.Formats.Dasl.Prolly.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.ShortKeySet

open Silmaril.Semantics (OrderedMap OrderedSet)

/-- The bound is in octets. Byte order is unsigned and lexicographic. -/
abbrev Bytes (limit : Fin 256) := { key : Prolly.ByteKey // key.length ≤ limit.val }

/-- The bound is on UTF-8 bytes, not character count. Equality is exact string
equality: neither NFC normalization nor case folding is applied. -/
abbrev Text (limit : Fin 256) := { key : String // key.utf8ByteSize ≤ limit.val }

def bounded {Key : Type} (size : Key → Nat) (limit : Fin 256) :
    Encode.TotalCodec {key : Key // size key ≤ limit.val} Key :=
  ⟨Subtype.val, (fun key => if fits : size key ≤ limit.val then some ⟨key, fits⟩ else none),
    fun ⟨_, fits⟩ => by simp [fits]⟩

def Bytes.ofBytes? (limit : Fin 256) : Prolly.ByteKey → Option (Bytes limit) :=
  (bounded List.length limit).decode?

def Text.ofString? (limit : Fin 256) : String → Option (Text limit) :=
  (bounded String.utf8ByteSize limit).decode?

variable {Name : Type} {limit : Fin 256}

def byteArrayCodec : Encode.TotalCodec (OrderedSet (Bytes limit)) (Shallow Name) :=
  Encode.setOf ((bounded List.length limit).then Prolly.byteKey)

def textArrayCodec : Encode.TotalCodec (OrderedSet (Text limit)) (Shallow Name) :=
  Encode.setOf ((bounded String.utf8ByteSize limit).then Encode.text)

def Text.octets (key : Text limit) : Bytes limit :=
  ⟨key.val.toUTF8.data.toList.map UInt8.toFin,
    by simpa only [List.length_map, ← Array.size_eq_length_toList, ByteArray.size_data,
      String.toUTF8_eq_toByteArray, String.size_toByteArray] using key.property⟩

def Text.fromOctets? (key : Bytes limit) : Option (Text limit) := do
  let text ← String.fromUTF8? (key.val.map UInt8.ofFin).toByteArray
  Text.ofString? limit text

def lengthPrefix (key : Bytes limit) : Fin 256 := ⟨key.val.length, key.property.trans_lt limit.isLt⟩

/-- One unsigned length octet, followed by exactly that many payload octets.
Even an empty key occupies one octet, so the end is unambiguous. -/
def pack : List (Bytes limit) → Prolly.ByteKey
  | [] => []
  | key :: tail => lengthPrefix key :: (key.val ++ pack tail)

def unpack (limit : Fin 256) : Nat → Prolly.ByteKey → Option (List (Bytes limit))
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, length :: tail =>
    if fits : length.val ≤ limit.val ∧ length.val ≤ tail.length then
      let key : Bytes limit := ⟨tail.take length.val, (List.length_take_le _ _).trans fits.1⟩
      (unpack limit fuel (tail.drop length.val)).map (key :: ·)
    else none

section Semantics

variable {Key : Type} [LinearOrder Key]

def members (layout : OrderedSet Key) : Finset Key := layout.keys.toFinset

def ofFinset (keys : Finset Key) : OrderedSet Key :=
  ⟨keys.sort.map (·, ()), List.pairwise_map.mpr (Finset.sortedLT_sort keys).pairwise⟩

def normalize (keys : List Key) : OrderedSet Key := ofFinset keys.toFinset

def contains (layout : OrderedSet Key) (key : Key) : Bool := decide (key ∈ layout.keys)

def cardinality (layout : OrderedSet Key) : Nat := layout.keys.length

end Semantics

end Silmaril.Formats.Dasl.ShortKeySet
