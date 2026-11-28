module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion

open Growth (Width)

structure Address where
  home : Nat
  slot : Nat
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- The slot map and the chronological list use the same addresses. An
overflow count records allocated links even when all their slots are empty. -/
structure Table where
  width : Width
  overflow : Nat → Nat
  cells : Address → Option Row
  order : List Address

def Table.emptyAt (width : Width) : Table := ⟨width, fun _ => 0, fun _ => none, []⟩

def Table.empty : Table := Table.emptyAt .one

def Table.extent (table : Table) (home : Nat) : Nat :=
  8 * (1 + table.overflow home)

def Table.entries (table : Table) : List Row :=
  table.order.filterMap table.cells

def Table.keys (table : Table) : List Value :=
  table.entries.map Row.key

def Table.slots (table : Table) (home : Nat) : List (Option Row) :=
  (List.range (table.extent home)).map fun index => table.cells ⟨home, index⟩

def Table.candidate (table : Table) (hash : UInt32) (index : Nat) : Option (Address × Row) := do
  let address := ⟨table.width.home hash, index⟩
  let row ← table.cells address
  if row.hash == hash then some (address, row) else none

def Table.candidates (table : Table) (hash : UInt32) : List (Address × Row) :=
  (List.range (table.extent (table.width.home hash))).filterMap (table.candidate hash)

/-- Every occupied cell is linked once and belongs to its hash's home.
Every linked address has an occupied, allocated cell. -/
structure WellFormed (table : Table) : Prop where
  unique : table.order.Nodup
  linked : ∀ address, address ∈ table.order ↔ (table.cells address).isSome
  placed : ∀ address row, table.cells address = some row →
    address.slot < table.extent address.home ∧ address.home = table.width.home row.hash
  bounded : table.order.length ≤ table.width.limit

def Table.write (table : Table) (address : Address) (cell : Option Row) : Table :=
  { table with cells := fun other => if other = address then cell else table.cells other }

def Table.unlink (table : Table) (address : Address) : Table :=
  { table.write address none with order := table.order.erase address }

def Table.replace (table : Table) (hit : Address × Row) (value : Value) : Table :=
  table.write hit.1 (some { hit.2 with value })

def lastVacant (empty : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | size + 1 => if empty size then some size else lastVacant empty size

def Table.vacancy (table : Table) (home : Nat) : Option Nat :=
  lastVacant (fun index => (table.cells ⟨home, index⟩).isNone) (table.extent home)

def Table.extend (table : Table) (home : Nat) : Table :=
  { table with overflow := fun other => if other = home then table.overflow other + 1 else table.overflow other }

def Table.link (table : Table) (address : Address) (row : Row) : Table :=
  { table.write address (some row) with order := table.order ++ [address] }

/-- The final vacancy encountered in a forward scan wins. A new overflow
block uses its first slot. Only a fresh entry is linked at the tail. -/
def Table.append (table : Table) (row : Row) : Table :=
  let home := table.width.home row.hash
  match table.vacancy home with
  | some index => table.link ⟨home, index⟩ row
  | none => (table.extend home).link ⟨home, table.extent home⟩ row

def Table.grow (table : Table) : Table :=
  table.entries.foldl Table.append (Table.emptyAt table.width.double)

def probeTable (heap : Heap) (table : Table) (key : Value) (hash : UInt32) :
    Except Error (Option (Address × Row)) :=
  (Comparison.probe
    (fun item => Comparison.equalAt heap Comparison.defaultDepth key item.2.key)
    (table.candidates hash)).mapError .runtime

def lookupWithHash (heap : Heap) (table : Table) (key : Value) :
    Except Error (UInt32 × Option (Address × Row)) := do
  let raw ← hashKey heap key
  let hash := storedHash raw
  let hit ← probeTable heap table key hash
  pure (hash, hit)

def get (heap : Heap) (table : Table) (key : Value) : Except Error (Option Value) :=
  (lookupWithHash heap table key).map fun (_, hit) => hit.map fun item => item.2.value

/-- The admitted table is initialized and has no active iterators or freeze.
Only a hit clears its slot and unlinks that address. -/
def delete (heap : Heap) (table : Table) (key : Value) : Except Error (Option Value × Table) := do
  let (_, hit) ← lookupWithHash heap table key
  match hit with
  | none => pure (none, table)
  | some item => pure (some item.2.value, table.unlink item.1)

def set (heap : Heap) (table : Table) (key value : Value) : Except Error Table := do
  let (hash, hit) ← lookupWithHash heap table key
  let row : Row := ⟨hash, key, value⟩
  match hit with
  | some item => pure (table.replace item value)
  | none =>
    if table.order.length < table.width.limit then pure (table.append row)
    else
      let expanded := table.grow
      match ← probeTable heap expanded key hash with
      | some item => pure (expanded.replace item value)
      | none => pure (expanded.append row)

def contains (heap : Heap) (table : Table) (key : Value) : Except Error Bool :=
  Option.isSome <$> observeLookup (get heap table key)

def equalWith (heap : Heap) (compare : Nat → Value → Value → Except Error Bool) :
    Nat → Table → Table → Except Error Bool
  | 0, _, _ => .error (.runtime .comparisonDepth)
  | depth + 1, left, right =>
    if left.order.length = right.order.length then compareRows (get heap right) (compare depth) left.entries
    else .ok false

end Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion
