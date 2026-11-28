module

public import Silmaril.Formats.Compression.Bits.Bit
public import Silmaril.Formats.Compression.Bits.BitstreamLemmas

/-! # Zstandard reverse bitstreams (RFC 8878 §3.1.1.3.2.1.2) -/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.ReverseBits

/-- The unread low bits of the current byte and the preceding bytes in
    reverse wire order. Reading never expands the remaining bytes into bits. -/
structure Cursor where
  current : UInt8
  count : Nat
  prior : List UInt8
  deriving DecidableEq, Repr

def Cursor.remaining (cursor : Cursor) : Nat :=
  cursor.count + 8 * cursor.prior.length

def Cursor.isEmpty (cursor : Cursor) : Bool :=
  cursor.count == 0 && cursor.prior.isEmpty

/-- Abstract bit order, from the next bit to the beginning of the wire. -/
def Cursor.bits (cursor : Cursor) : List Bit :=
  msbBits cursor.current.toNat cursor.count ++
    cursor.prior.flatMap (fun byte => msbBits byte.toNat 8)

/-- The final byte has a highest set bit at `width`, which is discarded
    along with every higher (zero) bit. -/
def StartWire (input : List UInt8) (cursor : Cursor) : Prop :=
  ∃ (front : List UInt8) (last : UInt8) (width : Nat),
    input = front ++ [last] ∧ width < 8 ∧
    2 ^ width ≤ last.toNat ∧ last.toNat < 2 ^ (width + 1) ∧
    cursor = ⟨last, width, front.reverse⟩

/-- Open the exact bitstream slice, using the highest set bit of its last
    byte as the end marker. Empty input and a zero last byte are invalid. -/
def start (input : List UInt8) : Option Cursor :=
  match input.reverse with
  | [] => none
  | last :: prior =>
    if last.toNat = 0 then none else some ⟨last, last.toNat.log2, prior⟩

namespace Internal

def next : Cursor → Option (Bit × Cursor)
  | ⟨_, 0, []⟩ => none
  | ⟨_, 0, byte :: tail⟩ => some (byte.toNat.testBit 7, ⟨byte, 7, tail⟩)
  | ⟨byte, n + 1, prior⟩ => some (byte.toNat.testBit n, ⟨byte, n, prior⟩)

def readLoop : Nat → Cursor → Nat → Option (Nat × Cursor)
  | 0, cursor, acc => some (acc, cursor)
  | width + 1, cursor, acc => do
    let (bit, tail) ← next cursor
    readLoop width tail (acc * 2 + bit.toNat)

end Internal

/-- Read one field backward through the stream. Its first bit is the field's
    most significant bit. The result is absent if the field does not fit. -/
def read (width : Nat) (cursor : Cursor) : Option (Nat × Cursor) :=
  Internal.readLoop width cursor 0

end Silmaril.Formats.Compression.Zstd.ReverseBits
