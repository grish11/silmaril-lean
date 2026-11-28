module

public import Silmaril.Formats.Compression.Bits.Bitstream
public import Silmaril.Formats.Compression.Zstd.FseTable.Defs

/-! # Zstandard transmitted normalized counts (RFC 8878 §4.1.1) -/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.FseTable.NCount

structure Limits where
  table : FseTable.Limits
  bytes : Nat
  expectedSymbols : Option Nat := none
  deriving DecidableEq, Repr

def Limits.byteCap (limits : Limits) : Nat := min limits.bytes 512

structure Prefix where
  distribution : Distribution
  bits : Nat
  bytes : Nat
  rest : List UInt8
  deriving DecidableEq, Repr

inductive Error where
  | truncated
  | byteLimit
  | accuracyLog
  | symbolLimit
  | wrongSymbolCount
  | tooFewSymbols
  | massOverflow
  | table (reason : FseTable.Error)
  deriving DecidableEq, Repr

/-- The variable count width and short-code cutoff for the remaining mass.
    The encoded probability value is the signed weight plus one. -/
def width (remaining : Nat) : Nat := (remaining + 1).log2

def threshold (remaining : Nat) : Nat := 2 ^ width remaining

def cutoff (remaining : Nat) : Nat := 2 * threshold remaining - 1 - (remaining + 1)

def longValue (remaining low high : Nat) : Nat :=
  if high = 0 then low else low + threshold remaining - cutoff remaining

def signedWeight (value : Nat) : Int := (value : Int) - 1

inductive WeightWire (remaining : Nat) : LSBReader → Int → LSBReader → Prop where
  | short {first last : LSBReader} {low : Nat} :
      first.readBits (width remaining) = some (low, last) → low < cutoff remaining →
      WeightWire remaining first (signedWeight low) last
  | long {first middle last : LSBReader} {low high : Nat} :
      first.readBits (width remaining) = some (low, middle) → cutoff remaining ≤ low →
      middle.readBits 1 = some (high, last) →
      WeightWire remaining first (signedWeight (longValue remaining low high)) last

/-- A repeat group ends with 0, 1 or 2. A group of 3 extends the run. -/
inductive ZeroRunWire : LSBReader → Nat → LSBReader → Prop where
  | stop {first last : LSBReader} {count : Nat} :
      first.readBits 2 = some (count, last) → count < 3 → ZeroRunWire first count last
  | more {first middle last : LSBReader} {count : Nat} :
      first.readBits 2 = some (3, middle) → ZeroRunWire middle count last →
      ZeroRunWire first (3 + count) last

/-- Accumulate normalized weights until the remaining table mass is zero.
    A zero weight has a mandatory repeat group, including a zero-length run. -/
inductive CountsWire : Nat → LSBReader → List Int → LSBReader → Prop where
  | done (cursor : LSBReader) : CountsWire 0 cursor [] cursor
  | nonzero {remaining : Nat} {first middle last : LSBReader} {weight : Int} {weights : List Int} :
      0 < remaining → WeightWire remaining first weight middle →
      weight ≠ 0 → slots weight ≤ remaining →
      CountsWire (remaining - slots weight) middle weights last →
      CountsWire remaining first (weight :: weights) last
  | zeros {remaining count : Nat} {first afterZero middle last : LSBReader} {weights : List Int} :
      0 < remaining → WeightWire remaining first 0 afterZero → ZeroRunWire afterZero count middle →
      CountsWire remaining middle weights last →
      CountsWire remaining first (0 :: (List.replicate count 0 ++ weights)) last

/-- The first four bits give the accuracy log minus five. Any unconsumed bits
    in the last touched byte are padding. The remainder starts at the next byte. -/
def PrefixWire (input : List UInt8) (result : Prefix) : Prop :=
  ∃ (used : List UInt8) (afterLog final : LSBReader),
    input = used ++ result.rest ∧ used.length = result.bytes ∧
      result.bytes = (result.bits + 7) / 8 ∧
      (LSBReader.mk 0 0 input 0).readBits 4 = some (result.distribution.log - 5, afterLog) ∧
      CountsWire result.distribution.size afterLog result.distribution.weights final ∧
      final.input = result.rest ∧ final.totalRead = result.bits

def Prefix.Valid (result : Prefix) (limits : Limits) (input : List UInt8) : Prop :=
  PrefixWire input result ∧ result.distribution.Valid limits.table ∧
    result.bytes ≤ limits.byteCap ∧ result.bits ≤ 8 * limits.byteCap ∧
    (∀ count, limits.expectedSymbols = some count → result.distribution.weights.length = count)

namespace Internal

def readField (cap : Nat) (cursor : LSBReader) (bits : Nat) :
    Except Error (Nat × LSBReader) :=
  if 8 * cap < cursor.totalRead + bits then .error .byteLimit
  else match cursor.readBits bits with
    | none => .error .truncated
    | some result => .ok result

def readWeight (cap remaining : Nat) (cursor : LSBReader) : Except Error (Int × LSBReader) := do
  let (low, tail) ← readField cap cursor (width remaining)
  if low < cutoff remaining then .ok (signedWeight low, tail)
  else
    let (high, rest) ← readField cap tail 1
    return (signedWeight (longValue remaining low high), rest)

def readZeros (cap : Nat) : Nat → Nat → LSBReader → Except Error (Nat × LSBReader)
  | 0, _, _ => .error .symbolLimit
  | fuel + 1, available, cursor => do
    let (group, tail) ← readField cap cursor 2
    if available < group then throw .symbolLimit
    if group = 3 then
      let (count, rest) ← readZeros cap fuel (available - 3) tail
      return (3 + count, rest)
    else .ok (group, tail)

def readCounts (cap : Nat) :
    Nat → Nat → Nat → LSBReader → Except Error (List Int × LSBReader)
  | _, _, 0, cursor => .ok ([], cursor)
  | 0, _, _ + 1, _ => .error .symbolLimit
  | _ + 1, 0, _ + 1, _ => .error .symbolLimit
  | fuel + 1, available + 1, remaining + 1, cursor => do
    let (weight, tail) ← readWeight cap (remaining + 1) cursor
    if remaining + 1 < slots weight then throw .massOverflow
    if weight = 0 then
      let (zeros, afterRun) ← readZeros cap (available + 1) available tail
      let (weights, rest) ← readCounts cap fuel (available - zeros) (remaining + 1) afterRun
      return (0 :: (List.replicate zeros 0 ++ weights), rest)
    else
      let (weights, rest) ← readCounts cap fuel available (remaining + 1 - slots weight) tail
      return (weight :: weights, rest)

end Internal

/-- Read one bounded normalized-count prefix without consuming the next
    table or sequence stream. Both limits apply before growing the result. -/
def read (limits : Limits) (input : List UInt8) : Except Error Prefix := do
  let (low, cursor) ← Internal.readField limits.byteCap ⟨0, 0, input, 0⟩ 4
  let log := low + 5
  if limits.table.logCap < log then throw .accuracyLog
  let (weights, rest) ← Internal.readCounts limits.byteCap limits.table.symbolCap
    limits.table.symbolCap (2 ^ log) cursor
  let distribution : Distribution := ⟨log, weights⟩
  if distribution.active < 2 then throw .tooFewSymbols
  if limits.expectedSymbols.any (· ≠ weights.length) then throw .wrongSymbolCount
  return ⟨distribution, rest.totalRead, (rest.totalRead + 7) / 8, rest.input⟩

/-- Build the table described by the checked prefix, retaining the same remainder. -/
def readTable (limits : Limits) (input : List UInt8) : Except Error (Prefix × Table) := do
  let result ← read limits input
  let table ← (build limits.table result.distribution).mapError Error.table
  return (result, table)

end Silmaril.Formats.Compression.Zstd.FseTable.NCount
