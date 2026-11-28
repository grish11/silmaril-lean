module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Growth

/-- The number of primary buckets is a power of two. Counts use naturals;
the profile models successful allocation and a representable Go entry count. -/
structure Width where
  log2 : Nat
  deriving DecidableEq, Repr

def Width.one : Width := ⟨0⟩
def Width.two : Width := ⟨1⟩

def Width.count (width : Width) : Nat := 2 ^ width.log2

def Width.double (width : Width) : Width := ⟨width.log2 + 1⟩

/-- Go requires at least eight entries and a load of at least 6.5. -/
def Width.limit (width : Width) : Nat := max 8 ((13 * width.count + 1) / 2)

theorem Width.limit_lt_double (width : Width) : width.limit < width.double.limit := by
  have positive := Nat.two_pow_pos width.log2
  simp only [limit, count, double, Nat.pow_succ]
  omega

def Width.home (width : Width) (hash : UInt32) : Nat :=
  hash.toNat % width.count

/-- Without deletion, the chronological rows determine all occupied slots. -/
structure Table where
  width : Width
  entries : List Row
  bounded : entries.length ≤ width.limit

def Table.empty : Table := ⟨.one, [], by decide⟩

def Table.keys (table : Table) : List Value :=
  table.entries.map Row.key

/-- Rank references by insertion order within the selected home chain. -/
def homeRows (width : Width) (entries : List Row) (hash : UInt32) : List (Row × Nat) :=
  entries.zipIdx.filter fun item => width.home item.1.hash == width.home hash

def Table.homeEntries (table : Table) (hash : UInt32) : List (Row × Nat) :=
  homeRows table.width table.entries hash

def primarySlots {α : Type} (entries : List α) : List (Option α) :=
  let primary := entries.take 8
  List.replicate (8 - primary.length) none ++ primary.reverse.map some

/-- An overflow block starts in slot zero. Later entries use its highest
free slot. -/
def overflowBlock {α : Type} (first : α) (later : List α) : List (Option α) :=
  some first :: (List.replicate (7 - later.length) none ++ later.reverse.map some)

def overflowSlots {α : Type} (entries : List α) : List (Option α) :=
  match entries with
  | [] => []
  | first :: later => overflowBlock first (later.take 7) ++ overflowSlots (later.drop 7)
termination_by entries.length

def physicalChain {α : Type} (entries : List α) : List (Option α) :=
  primarySlots entries ++ overflowSlots (entries.drop 8)

def slotOrder {α : Type} (entries : List α) : List α :=
  (physicalChain entries).filterMap id

def Table.slots (table : Table) (hash : UInt32) : List (Option (Row × Nat)) :=
  physicalChain (table.homeEntries hash)

def orderedCandidates (width : Width) (entries : List Row) (hash : UInt32) : List (Row × Nat) :=
  (slotOrder (homeRows width entries hash)).filter fun item => item.1.hash == hash

def Table.candidates (table : Table) (hash : UInt32) : List (Row × Nat) :=
  orderedCandidates table.width table.entries hash

/-- The placement produced by rehashing the original insertion order at the
wider mask. The stored rows already contain their normalized hash words. -/
def Table.grow (table : Table) : Table :=
  ⟨table.width.double, table.entries, Nat.le_trans table.bounded (Nat.le_of_lt table.width.limit_lt_double)⟩

def Table.insert (table : Table) (row : Row) (room : table.entries.length < table.width.limit) : Table :=
  ⟨table.width, table.entries ++ [row], by simpa using Nat.succ_le_of_lt room⟩

def Table.replace (table : Table) (hit : Row × Nat) (value : Value) : Table :=
  ⟨table.width, table.entries.set hit.2 { hit.1 with value }, by simpa using table.bounded⟩

def probeRows (heap : Heap) (width : Width) (entries : List Row) (key : Value) (hash : UInt32) :
    Except Error (Option (Row × Nat)) :=
  (Comparison.probe
    (fun candidate => Comparison.equalAt heap Comparison.defaultDepth key candidate.1.key)
    (orderedCandidates width entries hash)).mapError .runtime

def probeTable (heap : Heap) (table : Table) (key : Value) (hash : UInt32) :
    Except Error (Option (Row × Nat)) :=
  probeRows heap table.width table.entries key hash

def lookupWithHash (heap : Heap) (table : Table) (key : Value) :
    Except Error (UInt32 × Option (Row × Nat)) := do
  let word ← hashKey heap key
  let hash := storedHash word
  let hit ← probeTable heap table key hash
  pure (hash, hit)

/-- Replay only depends on the stored hash and original key. Each later
key must miss every earlier key with the same full hash. -/
def Replayable (heap : Heap) (entries : List Row) : Prop :=
  let keys := entries.map fun row => (row.hash, row.key)
  (∀ item ∈ keys, ∃ word, hashKey heap item.2 = .ok word ∧ storedHash word = item.1) ∧
    keys.Pairwise (fun earlier later => earlier.1 = later.1 →
      Comparison.equalAt heap Comparison.defaultDepth later.2 earlier.2 = .ok false)

/-- Each replay step recomputes its stored hash and probes the already
reinserted prefix before appending to the insertion list. -/
inductive Reinserts (heap : Heap) (width : Width) : List Row → List Row → Prop where
  | done (prefixRows : List Row) : Reinserts heap width prefixRows []
  | next {prefixRows : List Row} {row : Row} {remaining : List Row} {word : UInt32} :
      hashKey heap row.key = .ok word →
      storedHash word = row.hash →
      probeRows heap width prefixRows row.key row.hash = .ok none →
      prefixRows.length < width.limit →
      Reinserts heap width (prefixRows ++ [row]) remaining →
      Reinserts heap width prefixRows (row :: remaining)

def get (heap : Heap) (table : Table) (key : Value) : Except Error (Option Value) :=
  (lookupWithHash heap table key).map fun (_, hit) => hit.map fun item => item.1.value

/-- Probe before checking overload. Retry with the same hash after growing.
The old count fits the doubled width, so a retry can append without growing. -/
def set (heap : Heap) (table : Table) (key value : Value) : Except Error Table := do
  let (hash, hit) ← lookupWithHash heap table key
  let row : Row := ⟨hash, key, value⟩
  match hit with
  | some item => pure (table.replace item value)
  | none =>
    if room : table.entries.length < table.width.limit then
      pure (table.insert row room)
    else
      let expanded := table.grow
      match ← probeTable heap expanded key hash with
      | some item => pure (expanded.replace item value)
      | none => pure (expanded.insert row (Nat.lt_of_le_of_lt table.bounded table.width.limit_lt_double))

def contains (heap : Heap) (table : Table) (key : Value) : Except Error Bool :=
  Option.isSome <$> observeLookup (get heap table key)

def equalWith (heap : Heap) (compare : Nat → Value → Value → Except Error Bool) :
    Nat → Table → Table → Except Error Bool
  | 0, _, _ => .error (.runtime .comparisonDepth)
  | depth + 1, left, right =>
    if left.entries.length = right.entries.length then compareRows (get heap right) (compare depth) left.entries
    else .ok false

end Silmaril.Languages.Starlark.Lists.GoDictionary.Growth
