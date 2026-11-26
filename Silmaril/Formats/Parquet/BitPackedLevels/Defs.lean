module

public import Silmaril.Formats.Bytes

/-! Standalone reader for deprecated Parquet V1 BIT_PACKED (tag 4) levels. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.BitPackedLevels

structure Limits where
  levels : Nat
  bytes : Nat
  deriving DecidableEq, Repr

inductive Error where
  | invalidMaxLevel
  | countLimit
  | byteLimit
  | truncated
  | levelOutOfRange
  | trailingBytes
  deriving DecidableEq, Repr

def signedLimit : Nat := 2 ^ 31

def bitWidth (maxLevel : Nat) : Nat :=
  if maxLevel = 0 then 0 else maxLevel.log2 + 1

def byteCount (maxLevel count : Nat) : Nat :=
  (count * bitWidth maxLevel + 7) / 8

/-- Position zero is the high bit of the first byte. -/
def wireBit (packed : Bytes) (position : Nat) : Nat :=
  let byte := (packed.data[position / 8]?.getD 0).toNat
  byte / 2 ^ (7 - position % 8) % 2

/-- Positional value of a fixed-width MSB-first field. This wire model weights
each bit by the number of bits to its right. -/
def wireCode (packed : Bytes) (start : Nat) : Nat → Nat
  | 0 => 0
  | width + 1 => wireBit packed start * 2 ^ width + wireCode packed (start + 1) width

/-- Exact packed level bytes, including any unused low bits of the final octet.
Only the bit range of each requested level contributes to its value. -/
structure Wire (maxLevel count : Nat) (packed : Bytes) (levels : List Nat) : Prop where
  extent : packed.length = byteCount maxLevel count
  countFits : levels.length = count
  order : ∀ (i : Nat) (hi : i < levels.length),
    levels[i] = wireCode packed (i * bitWidth maxLevel) (bitWidth maxLevel)
  bounds : ∀ level ∈ levels, level ≤ maxLevel

namespace Internal

def takeBytes (source : Bytes) (size : Nat) : Bytes := ⟨source.data.extract 0 size⟩

def dropBytes (source : Bytes) (size : Nat) : Bytes := ⟨source.data.extract size source.length⟩

/-- Advance through a single field, shifting the accumulated code left. -/
def readCode (data : ByteArray) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | width + 1, position, acc =>
    let byte := (data[position / 8]?.getD 0).toNat
    let digit := (byte >>> (7 - position % 8)) % 2
    readCode data width (position + 1) (2 * acc + digit)

def codes (packed : Bytes) (width count : Nat) : List Nat :=
  List.ofFn fun i : Fin count => readCode packed.data width (i.val * width) 0

end Internal

/-- A V1 tag-4 section occupies a count-derived prefix with no length word.
Check the count and byte budgets before slicing and decoding. Unused low bits
of the last byte are ignored. -/
def readPrefix (maxLevel count : Nat) (limits : Limits) (source : Bytes) :
    Except Error (List Nat × Bytes) :=
  if signedLimit ≤ maxLevel then .error .invalidMaxLevel
  else if signedLimit ≤ count ∨ limits.levels < count then .error .countLimit
  else
    let size := byteCount maxLevel count
    if limits.bytes < size then .error .byteLimit
    else if source.length < size then .error .truncated
    else
      let packed := Internal.takeBytes source size
      let levels := Internal.codes packed (bitWidth maxLevel) count
      if levels.all (fun level => level ≤ maxLevel) then
        .ok (levels, Internal.dropBytes source size)
      else .error .levelOutOfRange

/-- Decode an already delimited level section. -/
def readExact (maxLevel count : Nat) (limits : Limits) (source : Bytes) :
    Except Error (List Nat) := do
  let (levels, rest) ← readPrefix maxLevel count limits source
  if rest.length = 0 then pure levels else throw .trailingBytes

end Silmaril.Formats.Parquet.BitPackedLevels
