module

public import Silmaril.Languages.Starlark.Lists.Comparison.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists.GoDictionary

inductive Error where
  | unsupportedKey (key : Value)
  | tupleGraph
  | capacity
  | runtime (error : Lists.Error)
  deriving DecidableEq, Repr

/-- Small ints contribute the unsigned word of the signed value. Big ints
contribute the low magnitude word, including on the negative side. -/
def intLowWord (value : Int) : UInt32 :=
  if -(2 ^ 31) ≤ value ∧ value < 2 ^ 31 then UInt32.ofNat (value % 2 ^ 32).toNat
  else UInt32.ofNat value.natAbs

def intHash (value : Int) : UInt32 :=
  12582917 * (intLowWord value + 3)

/-- The pin uses an int64 conversion in range and rational division outside
it. The bounds are written in the binary64 decoder's exact units. -/
def finiteInt (units : Int) : Int :=
  let scale : Int := 2 ^ 1074
  if -(2 ^ 63 * scale) ≤ units ∧ units < 2 ^ 63 * scale then units.tdiv scale
  else units / scale

def numberHash : Binary64.Number → UInt32
  | .finite units => intHash (finiteInt units)
  | .negativeInfinity | .positiveInfinity | .nan => 1618033

def scalarHash : Starlark.Value → UInt32
  | .none => 0
  | .bool flag => if flag then 1 else 0
  | .int value => intHash value
  | .float bits => numberHash (Binary64.decode bits)

/-- The tuple mixer consumes raw field hashes before the table reserves zero. -/
def mixFields (increment : UInt32) : List UInt32 → UInt32 → UInt32 → UInt32
  | [], hash, _ => hash
  | word :: rest, hash, mult =>
    mixFields increment rest (hash ^^^ (word * mult)) (mult + increment)

def tupleHash (words : List UInt32) : UInt32 :=
  mixFields (82520 + 2 * UInt32.ofNat words.length) words 0x345678 1000003

/-- The budget bounds tuple graph reads. Every path in a well-formed
acyclic heap of this size fits, including its terminal scalar. -/
def hashAt (heap : Heap) : Nat → Value → Except Error UInt32
  | 0, _ => .error .tupleGraph
  | _ + 1, .scalar value => .ok (scalarHash value)
  | depth + 1, .tuple address => do
    let fields ← (heap.tupleFields address).mapError .runtime
    let words ← fields.mapM (hashAt heap depth)
    pure (tupleHash words)
  | _, key => .error (.unsupportedKey key)

def hashKey (heap : Heap) (key : Value) : Except Error UInt32 :=
  hashAt heap (heap.size + 1) key

/-- Bucket slots reserve zero for absence. -/
def storedHash (hash : UInt32) : UInt32 :=
  if hash = 0 then 1 else hash

structure Row where
  hash : UInt32
  key : Value
  value : Value
  deriving DecidableEq, Repr

/-- An eight-slot, no-deletion bucket stores its occupied suffix in ascending
slot order. Entries are added at the front of the suffix. -/
structure Bucket where
  rows : List Row
  bounded : rows.length ≤ 8

def Bucket.empty : Bucket := ⟨[], by decide⟩

def Bucket.slots (bucket : Bucket) : List (Option Row) :=
  List.replicate (8 - bucket.rows.length) none ++ bucket.rows.map some

def Bucket.keys (bucket : Bucket) : List Value :=
  bucket.rows.reverse.map Row.key

def Bucket.candidates (bucket : Bucket) (hash : UInt32) : List (Row × Nat) :=
  bucket.rows.zipIdx.filter fun candidate => candidate.1.hash == hash

def Bucket.insert (bucket : Bucket) (row : Row) (room : bucket.rows.length < 8) : Bucket :=
  ⟨row :: bucket.rows, by change bucket.rows.length + 1 ≤ 8; omega⟩

def Bucket.replace (bucket : Bucket) (hit : Row × Nat) (value : Value) : Bucket :=
  ⟨bucket.rows.set hit.2 { hit.1 with value }, by simpa using bucket.bounded⟩

/-- Lookup and insertion use the same reached key comparisons. The index
identifies the slot for replacement. -/
def lookupWithHash (heap : Heap) (bucket : Bucket) (key : Value) :
    Except Error (UInt32 × Option (Row × Nat)) := do
  let hash ← hashKey heap key
  let digest := storedHash hash
  let hit ← (Comparison.probe
    (fun candidate => Comparison.equalAt heap Comparison.defaultDepth key candidate.1.key)
    (bucket.candidates digest)).mapError .runtime
  pure (digest, hit)

def get (heap : Heap) (bucket : Bucket) (key : Value) : Except Error (Option Value) :=
  (lookupWithHash heap bucket key).map fun (_, hit) => hit.map fun item => item.1.value

/-- A miss on a full bucket would grow the table in Go. It is a profile
rejection here. An existing key can still be replaced at capacity. -/
def set (heap : Heap) (bucket : Bucket) (key value : Value) : Except Error Bucket := do
  let (digest, hit) ← lookupWithHash heap bucket key
  match hit with
  | some item => pure (bucket.replace item value)
  | none =>
    if room : bucket.rows.length < 8 then pure (bucket.insert ⟨digest, key, value⟩ room)
    else throw .capacity

/-- For admitted keys the reached Go comparison failure is a depth error.
Profile exclusions and malformed model reads retain their own results. -/
def observeLookup {α : Type} : Except Error (Option α) → Except Error (Option α)
  | .error (.runtime .comparisonDepth) => .ok none
  | out => out

def contains (heap : Heap) (bucket : Bucket) (key : Value) : Except Error Bool :=
  Option.isSome <$> observeLookup (get heap bucket key)

def compareRows (getValue : Value → Except Error (Option Value))
    (compare : Value → Value → Except Error Bool) : List Row → Except Error Bool
  | [] => .ok true
  | row :: later => do
    match ← observeLookup (getValue row.key) with
    | none => pure false
    | some value =>
      if ← compare row.value value then compareRows getValue compare later
      else pure false

def equalValues (heap : Heap) (right : Bucket)
    (compare : Value → Value → Except Error Bool) : List Row → Except Error Bool :=
  compareRows (get heap right) compare

/-- Outer dictionary equality consumes one level for the outer comparison.
The supplied value comparator receives the remaining depth. -/
def equalWith (heap : Heap) (compare : Nat → Value → Value → Except Error Bool) :
    Nat → Bucket → Bucket → Except Error Bool
  | 0, _, _ => .error (.runtime .comparisonDepth)
  | depth + 1, left, right =>
    if left.rows.length = right.rows.length then equalValues heap right (compare depth) left.rows.reverse
    else .ok false

end Silmaril.Languages.Starlark.Lists.GoDictionary
