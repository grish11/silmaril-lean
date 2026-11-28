module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction.Defs
public import Silmaril.Languages.Starlark.Lists.Denotation.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Guards

inductive Rejection where
  | frozen
  | activeIteration
  deriving DecidableEq, Repr

def Rejection.canonicalError (reason : Rejection) (address : Lists.Address) : Lists.Error :=
  match reason with
  | .frozen => .frozen address
  | .activeIteration => .activeIteration address

inductive MutationError where
  | guard (reason : Rejection)
  | table (error : Error)
  deriving DecidableEq, Repr

/-- Go's zero-value dictionary has no allocated table. An initialized empty
dictionary has a table, even though both states have the same live rows. -/
structure Table where
  contents : Option Deletion.Table := none
  frozen : Bool := false
  activeIterators : Nat := 0

def Table.rows (table : Table) : Deletion.Table :=
  table.contents.getD Deletion.Table.empty

def Table.initialize (table : Table) : Table :=
  { table with contents := some table.rows }

def Table.rejection (table : Table) : Option Rejection :=
  if table.frozen then some .frozen
  else if 0 < table.activeIterators then some .activeIteration
  else none

/-- Frozen Go tables yield keys without incrementing their iterator count. -/
def Table.enterIterator (table : Table) : Table :=
  if table.frozen then table else { table with activeIterators := table.activeIterators + 1 }

abbrev MutationOutcome (α : Type) := EStateM.Result MutationError Table α

/-- This primitive receives evaluated operands. Go checks the guards, then
initializes storage, then attempts the hash and probe. -/
def set (heap : Heap) (table : Table) (key value : Value) : MutationOutcome Unit :=
  match table.rejection with
  | some reason => .error (.guard reason) table
  | none =>
    let ready := table.initialize
    match Deletion.set heap ready.rows key value with
    | .error error => .error (.table error) ready
    | .ok next => .ok () { ready with contents := some next }

/-- On an unallocated table Go deletion returns a miss before hashing. -/
def delete (heap : Heap) (table : Table) (key : Value) : MutationOutcome (Option Value) :=
  match table.rejection with
  | some reason => .error (.guard reason) table
  | none =>
    match table.contents with
    | none => .ok none table
    | some rows =>
      match Deletion.delete heap rows key with
      | .error error => .error (.table error) table
      | .ok (removed, next) => .ok removed { table with contents := some next }

/-- A zero-value Go table can represent a live empty canonical dictionary.
An absent canonical receiver or binding has its own evaluation error. -/
structure Related (state : State) (address : Lists.Address) (table : Table)
    (entries : List Entry) : Prop where
  cell : state.heap[address]? = some ⟨.dict entries, table.frozen⟩
  active : table.frozen = false → (0 < table.activeIterators ↔ address ∈ state.iterators)
  rows : Abstraction.Related state.heap Abstraction.scalarProfile table.rows entries

/-- These key families are unhashable on both sides. -/
inductive Unhashable : Value → Prop where
  | list (address : Lists.Address) : Unhashable (.list address)
  | dict (address : Lists.Address) : Unhashable (.dict address)
  | range (span : RangeValue) : Unhashable (.range span)

/-- Assignment outcomes correspond by reason and reached state. A reached
hash failure can initialize Go storage while leaving the canonical state intact. -/
inductive AssignsTogether (state : State) (address : Lists.Address) (table : Table)
    (entries : List Entry) : MutationOutcome Unit → Outcome Unit → Prop where
  | rejected (reason : Rejection) : Related state address table entries →
      AssignsTogether state address table entries
        (.error (.guard reason) table) (.error (reason.canonicalError address) state)
  | unhashable (key : Value) : Unhashable key → Related state address table.initialize entries →
      AssignsTogether state address table entries
        (.error (.table (.unsupportedKey key)) table.initialize) (.error (.unhashableKey key) state)
  | assigned {after : State} {next : Table} {rows : List Entry} :
      Related after address next rows →
      AssignsTogether state address table entries (.ok () next) (.ok () after)

end Silmaril.Languages.Starlark.Lists.GoDictionary.Guards
