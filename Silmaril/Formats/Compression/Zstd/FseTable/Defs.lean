module

/-! # Zstandard FSE decoding tables

RFC 8878 §4.1.1 and §3.1.1.3.2.2. Construct bounded decoding tables
from normalized weights, including the predefined sequence tables.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.FseTable

structure Limits where
  accuracyLog : Nat
  symbols : Nat
  deriving DecidableEq, Repr

def Limits.logCap (limits : Limits) : Nat := min limits.accuracyLog 9
def Limits.symbolCap (limits : Limits) : Nat := min limits.symbols 256

structure Distribution where
  log : Nat
  weights : List Int
  deriving DecidableEq, Repr

def Distribution.size (dist : Distribution) : Nat := 2 ^ dist.log

/-- A low-probability symbol occupies one slot, like an ordinary weight of
    one, but its slot is reserved at the high end of the table. -/
def slots (weight : Int) : Nat :=
  if weight = -1 then 1 else weight.toNat

def Distribution.mass (dist : Distribution) : Nat := (dist.weights.map slots).sum

def Distribution.active (dist : Distribution) : Nat :=
  (dist.weights.filter (· != 0)).length

def Distribution.Valid (dist : Distribution) (limits : Limits) : Prop :=
  5 ≤ dist.log ∧ dist.log ≤ limits.logCap ∧ dist.weights.length ≤ limits.symbolCap ∧
    (∀ weight ∈ dist.weights, -1 ≤ weight) ∧ 2 ≤ dist.active ∧ dist.mass = dist.size

structure Row where
  symbol : Nat
  bits : Nat
  baseline : Nat
  deriving DecidableEq, Repr

structure Table where
  log : Nat
  rows : List Row
  deriving DecidableEq, Repr

inductive Error where
  | accuracyLog
  | symbolLimit
  | invalidWeight
  | tooFewSymbols
  | wrongMass
  | invalidLayout
  | invalidRows
  | invalidMultiplicity
  | unsupportedMode (mode : UInt8)
  deriving DecidableEq, Repr

/-- The RFC state walk starts at zero. Low-probability symbols reserve the
    final slots in reverse symbol order, so the walk skips those slots. -/
def placements (dist : Distribution) : List (Nat × Nat) :=
  let indexed := dist.weights.zipIdx
  let low := indexed.filterMap fun (weight, symbol) => if weight = -1 then some symbol else none
  let ordinary := indexed.flatMap fun (weight, symbol) => List.replicate weight.toNat symbol
  let size := dist.size
  let high := size - low.length
  let step := size / 2 + size / 8 + 3
  let walk := (List.range size).map fun i => (i * step) % size
  ((walk.filter (· < high)).zip ordinary) ++ ((List.range' high low.length).zip low.reverse)

/-- A full spread assigns every state once according to the canonical
    placement walk. -/
def LayoutWire (dist : Distribution) (symbols : List Nat) : Prop :=
  ∃ ordered : List (Nat × Nat),
    ordered.Perm (placements dist) ∧ ordered.map Prod.fst = List.range dist.size ∧
      symbols = ordered.map Prod.snd

/-- Assign the baseline and width in state order. The ordinal starts at the
    symbol's slot count and increases on each occurrence of that symbol. -/
def rowFor (dist : Distribution) (symbols : List Nat) (state symbol : Nat) : Row :=
  let ordinal := slots (dist.weights[symbol]?.getD 0) + (symbols.take state).count symbol
  let bits := dist.log - ordinal.log2
  ⟨symbol, bits, ordinal * 2 ^ bits - dist.size⟩

def TableWire (dist : Distribution) (table : Table) : Prop :=
  ∃ symbols, LayoutWire dist symbols ∧ table.log = dist.log ∧
    table.rows = symbols.mapIdx (rowFor dist symbols)

def Row.Valid (row : Row) (dist : Distribution) : Prop :=
  row.symbol < dist.weights.length ∧ row.bits ≤ dist.log ∧ row.baseline + 2 ^ row.bits ≤ dist.size

instance (row : Row) (dist : Distribution) : Decidable (row.Valid dist) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def Table.WellFormed (table : Table) (dist : Distribution) : Prop :=
  table.log = dist.log ∧ table.rows.length = dist.size ∧
    (∀ row ∈ table.rows, row.Valid dist) ∧
    ∀ symbol weight, dist.weights[symbol]? = some weight →
      (table.rows.map Row.symbol).count symbol = slots weight

namespace Internal

def validate (limits : Limits) (dist : Distribution) : Except Error Unit :=
  if dist.log < 5 ∨ limits.logCap < dist.log then .error .accuracyLog
  else if limits.symbolCap < dist.weights.length then .error .symbolLimit
  else if !(dist.weights.all fun weight => decide (-1 ≤ weight)) then .error .invalidWeight
  else if dist.active < 2 then .error .tooFewSymbols
  else if dist.mass ≠ dist.size then .error .wrongMass
  else .ok ()

def assemble (dist : Distribution) : Except Error Table :=
  let ordered := (placements dist).mergeSort fun left right => left.1 ≤ right.1
  if ordered.map Prod.fst ≠ List.range dist.size then .error .invalidLayout
  else
    let symbols := ordered.map Prod.snd
    let rows := symbols.mapIdx (rowFor dist symbols)
    if !(rows.all fun row => decide (row.Valid dist)) then .error .invalidRows
    else
      let entries := rows.map Row.symbol
      if !(dist.weights.zipIdx.all fun (weight, symbol) => entries.count symbol == slots weight) then
        .error .invalidMultiplicity
      else .ok ⟨dist.log, rows⟩

end Internal

/-- Check the distribution before allocating state slots. The ordered layout,
    transition intervals and symbol multiplicities are checked on completion. -/
def build (limits : Limits) (dist : Distribution) : Except Error Table := do
  Internal.validate limits dist
  Internal.assemble dist

inductive Alphabet where
  | literalLength
  | offset
  | matchLength
  deriving DecidableEq, Repr

/-- The three predefined sequence distributions from RFC 8878 §3.1.1.3.2.2. -/
def predefined : Alphabet → Distribution
  | .literalLength => ⟨6,
      [4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2,
       2, 2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 1, 1, 1, -1, -1, -1, -1]⟩
  | .offset => ⟨5,
      [1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
       -1, -1, -1, -1, -1]⟩
  | .matchLength => ⟨6,
      [1, 4, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
       1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
       -1, -1, -1, -1, -1, -1, -1]⟩

/-- A predefined-mode table occupies zero bytes after its mode field. The
    caller supplies the already extracted field for this alphabet. -/
def selectPredefined (limits : Limits) (alphabet : Alphabet) (mode : UInt8)
    (input : List UInt8) : Except Error (Table × List UInt8) :=
  if mode = 0 then (build limits (predefined alphabet)).map (·, input)
  else .error (.unsupportedMode mode)

end Silmaril.Formats.Compression.Zstd.FseTable
