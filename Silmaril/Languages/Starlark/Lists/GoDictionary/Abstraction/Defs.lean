module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction

structure KeyObservation where
  code : Key
  hash : UInt32
  deriving DecidableEq, Repr

/-- A profile supplies a canonical code and normalized Go hash for each admitted key. -/
abbrev KeyProfile := Value → Option KeyObservation

/-- All admitted keys hash successfully. Reached key comparisons are total
and agree with the codes, and code equality implies stored-hash equality. -/
structure Coherent (heap : Heap) (profile : KeyProfile) : Prop where
  canonical : ∀ key obs, profile key = some obs →
    ({ heap := heap } : State).keyOf key = .ok obs.code
  hashes : ∀ key obs, profile key = some obs →
    ∃ word, hashKey heap key = .ok word ∧ storedHash word = obs.hash
  compares : ∀ left right a b, profile left = some a → profile right = some b → a.hash = b.hash →
    Comparison.equalAt heap Comparison.defaultDepth left right = .ok (a.code == b.code)
  sameHash : ∀ left right a b, profile left = some a → profile right = some b →
    a.code = b.code → a.hash = b.hash

def scalarProfile : KeyProfile
  | .scalar value => some ⟨[.scalar (ScalarKey.ofValue value)], storedHash (scalarHash value)⟩
  | _ => none

/-- Total only on admitted rows with the correct stored hash. The original
key and value are copied verbatim into the canonical entry. -/
def observeRow (profile : KeyProfile) (row : Row) : Option Entry := do
  let obs ← profile row.key
  if row.hash = obs.hash then some ⟨row.key, obs.code, row.value⟩ else none

def observeCell (profile : KeyProfile) (table : Deletion.Table) (address : Deletion.Address) :
    Option Entry :=
  (table.cells address).bind (observeRow profile)

structure Related (heap : Heap) (profile : KeyProfile) (table : Deletion.Table)
    (entries : List Entry) : Prop where
  layout : Deletion.WellFormed table
  replay : Growth.Replayable heap table.entries
  ordered : table.order.map (observeCell profile table) = entries.map some
  unique : Comparison.UniqueKeyCodes entries

/-- Read the full canonical entry selected by the physical table. -/
def lookupEntry (heap : Heap) (profile : KeyProfile) (table : Deletion.Table) (key : Value) :
    Except Error (Option Entry) :=
  (Deletion.lookupWithHash heap table key).map fun (_, hit) =>
    hit.bind fun item => observeRow profile item.2

end Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction
