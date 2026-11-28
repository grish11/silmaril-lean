module

public import Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix.Defs

/-! # Zstandard interleaved FSE Huffman weights

RFC 8878 §4.2.1.2. Decode explicit weights in symbol order. The caller
can pass them to the separate inferred-weight tree checker.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.FseWeights

open ReverseBits (Cursor)

structure Prefix where
  weights : List Nat
  consumed : Nat
  rest : List UInt8
  deriving DecidableEq, Repr

inductive Error where
  | description (reason : FsePrefix.Error)
  | weightLimit
  | invalidState
  | invalidTransition
  deriving DecidableEq, Repr

/-- The final Huffman weight is inferred separately. -/
def weightCap (limit : Nat) : Nat := min limit 255

/-- The first state is active. A complete field updates that state and
    swaps turns. At the first short field the missing low bits are zeros
    and the updated state is discarded. The final pair is the active
    symbol followed by the waiting symbol, with no field from the latter. -/
inductive Emits (table : FseTable.Table) : Nat → Nat → List Bit → List Nat → Prop where
  | step {active waiting : Nat} {bits : List Bit} {row : FseTable.Row} {tail : List Nat} :
      table.rows[active]? = some row → row.bits ≤ bits.length →
      row.baseline + Bit.bitsToNatMSB (bits.take row.bits) < table.rows.length →
      Emits table waiting (row.baseline + Bit.bitsToNatMSB (bits.take row.bits))
        (bits.drop row.bits) tail →
      Emits table active waiting bits (row.symbol :: tail)
  | overflow {active waiting : Nat} {bits : List Bit} {row final : FseTable.Row} :
      table.rows[active]? = some row → bits.length < row.bits →
      table.rows[waiting]? = some final →
      Emits table active waiting bits [row.symbol, final.symbol]

def Wire (input : List UInt8) (result : Prefix) : Prop :=
  ∃ parsedPrefix : FsePrefix.Prefix, FsePrefix.PrefixWire input parsedPrefix ∧
    result.consumed = parsedPrefix.consumed ∧ result.rest = parsedPrefix.rest ∧
    Emits parsedPrefix.setup.table parsedPrefix.setup.states.first parsedPrefix.setup.states.second
      parsedPrefix.setup.cursor.bits result.weights

namespace Internal

/-- The remaining weight budget is fuel, including for zero-bit rows. -/
def emit (table : FseTable.Table) : Nat → Nat → Nat → Cursor → Except Error (List Nat)
  | 0, _, _, _ => .error .weightLimit
  | fuel + 1, active, waiting, cursor => do
    let some row := table.rows[active]? | throw .invalidState
    if cursor.remaining < row.bits then
      if fuel = 0 then throw .weightLimit
      let some final := table.rows[waiting]? | throw .invalidState
      return [row.symbol, final.symbol]
    else
      let some (extra, rest) := ReverseBits.read row.bits cursor | throw .invalidTransition
      let tail ← emit table fuel waiting (row.baseline + extra) rest
      return row.symbol :: tail

end Internal

/-- Decode exactly the declared FSE description. Initialization and marker
    errors are distinct from the terminal short field after initialization.
    The returned weights are the transmitted prefix of the Huffman tree. -/
def read (byteLimit weightLimit : Nat) (input : List UInt8) : Except Error Prefix := do
  let parsedPrefix ← (FsePrefix.read byteLimit input).mapError .description
  let setup := parsedPrefix.setup
  let weights ← Internal.emit setup.table (weightCap weightLimit)
    setup.states.first setup.states.second setup.cursor
  return ⟨weights, parsedPrefix.consumed, parsedPrefix.rest⟩

end Silmaril.Formats.Compression.Zstd.Huffman.FseWeights
