module

public import Silmaril.Semantics.Naming.Defs

@[expose] public section

namespace Silmaril.Semantics.Arena

variable {Key Name Payload : Type}

/-- An occupied slot may hold a name, a resident payload, both, or neither.
`none : Option (Slot Name Payload)` is a hole, not an empty occupied slot. -/
structure Slot (Name Payload : Type) where
  name : Option Name
  payload : Option Payload
  deriving DecidableEq, Repr

abbrev State (Key Name Payload : Type) := Key → Option (Slot Name Payload)

abbrev ByteState (Key Name : Type) := State Key Name ByteArray

inductive Fault where
  | occupied
  | vacant
  | outOfBounds
  deriving DecidableEq, Repr

/-- Reserve requires a hole. The other edits require occupancy. Replacement
explicitly supplies the new name: it does not carry an old claim forward. -/
inductive Edit (Name Payload : Type) where
  | reserve (name : Option Name)
  | replace (slot : Slot Name Payload)
  | erasePayload
  | clear

namespace Edit

/-- No selected name means a successful anonymous write, not a CAS binding.
This constructor does not certify the oracle or compute a particular hash. -/
def write (assign : Payload → Option Name) (payload : Payload) : Edit Name Payload :=
  .replace ⟨assign payload, some payload⟩

def apply : Edit Name Payload → Option (Slot Name Payload) → Except Fault (Option (Slot Name Payload))
  | .reserve name, none => .ok (some ⟨name, none⟩)
  | .reserve _, some _ => .error .occupied
  | .replace next, some _ => .ok (some next)
  | .erasePayload, some old => .ok (some ⟨old.name, none⟩)
  | .clear, some _ => .ok none
  | _, none => .error .vacant

end Edit

namespace State

def empty : State Key Name Payload := fun _ => none

/-- The outer lookup still distinguishes a hole from an anonymous slot.
This projection alone intentionally does not. -/
def keyName (arena : State Key Name Payload) (key : Key) : Option Name :=
  (arena key).bind Slot.name

/-- Unchecked point update, used to define guarded edits. -/
def replaceAt [DecidableEq Key] (arena : State Key Name Payload) (key : Key)
    (next : Option (Slot Name Payload)) : State Key Name Payload :=
  fun index => if key = index then next else arena index

def step [DecidableEq Key] (arena : State Key Name Payload) (key : Key) (edit : Edit Name Payload) :
    Except Fault (State Key Name Payload) := (edit.apply (arena key)).map (arena.replaceAt key)

/-- Only co-present names and resident payloads contribute witnesses. A
name-only reservation is not a statement of presence, absence or integrity. -/
def observations (arena : State Key Name Payload) : Naming.Relation Name Payload := fun name payload =>
  ∃ key, arena key = some ⟨some name, some payload⟩

def AdmittedBy (arena : State Key Name Payload) (reference : Naming.Relation Name Payload) : Prop :=
  Naming.Subset arena.observations reference

end State

/-- The exclusive bound is capacity, not the number of occupied slots. -/
abbrev Bounded (limit : Nat) (Name Payload : Type) :=
  { arena : State Nat Name Payload // ∀ index, limit ≤ index → arena index = none }

abbrev Dense (limit : Nat) (Name Payload : Type) :=
  { cells : Array (Option (Slot Name Payload)) // cells.size = limit }

variable {limit : Nat}

namespace Bounded

def replaceAt (arena : Bounded limit Name Payload) (index : Nat) (inside : index < limit)
    (next : Option (Slot Name Payload)) : Bounded limit Name Payload :=
  ⟨State.replaceAt arena.val index next, fun query outside => by
    have different := Nat.ne_of_lt (Nat.lt_of_lt_of_le inside outside)
    simp [State.replaceAt, different, arena.property query outside]⟩

def step (arena : Bounded limit Name Payload) (index : Nat) (edit : Edit Name Payload) :
    Except Fault (Bounded limit Name Payload) :=
  if inside : index < limit then (edit.apply (arena.val index)).map (arena.replaceAt index inside)
  else .error .outOfBounds

/-- Allocate at the old bound, not at any previously freed index. -/
def append (arena : Bounded limit Name Payload) (next : Slot Name Payload) : Bounded (limit + 1) Name Payload :=
  ⟨State.replaceAt arena.val limit (some next), fun query outside => by
    have different := Nat.ne_of_lt (Nat.lt_of_succ_le outside)
    simp [State.replaceAt, different, arena.property query (Nat.le_of_lt (Nat.lt_of_succ_le outside))]⟩

def toDense (arena : Bounded limit Name Payload) : Dense limit Name Payload :=
  ⟨Array.ofFn (fun index : Fin limit => arena.val index), Array.size_ofFn⟩

end Bounded

namespace Dense

def read (arena : Dense limit Name Payload) (index : Nat) : Option (Slot Name Payload) :=
  arena.val[index]?.getD none

def toBounded (arena : Dense limit Name Payload) : Bounded limit Name Payload :=
  ⟨arena.read, fun index outside => by
    have past : arena.val.size ≤ index := arena.property.symm ▸ outside
    simp [read, Array.getElem?_eq_none past]⟩

/-- Low-level array update; out-of-bounds indices are unchanged. Use `step`
to enforce occupancy rules and report faults. -/
def replaceAt (arena : Dense limit Name Payload) (index : Nat) (next : Option (Slot Name Payload)) :
    Dense limit Name Payload :=
  ⟨arena.val.setIfInBounds index next, by simpa only [Array.size_setIfInBounds] using arena.property⟩

def step (arena : Dense limit Name Payload) (index : Nat) (edit : Edit Name Payload) :
    Except Fault (Dense limit Name Payload) :=
  if index < limit then (edit.apply (arena.read index)).map (arena.replaceAt index)
  else .error .outOfBounds

def append (arena : Dense limit Name Payload) (next : Slot Name Payload) : Dense (limit + 1) Name Payload :=
  ⟨arena.val.push (some next), by simp [arena.property]⟩

/-- Plain arrays encode the no-hole case. No in-band sentinel is used. -/
def packed (slots : Array (Slot Name Payload)) : Dense slots.size Name Payload :=
  ⟨slots.map some, Array.size_map⟩

/-- This only constrains occupancy. Both fields of an occupied slot may be empty. -/
def NoHoles (arena : Dense limit Name Payload) : Prop :=
  ∀ index : Fin limit, (arena.read index).isSome = true

def packExact (slots : { slots : Array (Slot Name Payload) // slots.size = limit }) : Dense limit Name Payload :=
  ⟨slots.val.map some, Array.size_map.trans slots.property⟩

def unpack (arena : Dense limit Name Payload) (occupied : arena.NoHoles) :
    { slots : Array (Slot Name Payload) // slots.size = limit } :=
  ⟨Array.ofFn (fun index : Fin limit => (arena.read index).get (occupied index)), Array.size_ofFn⟩

end Dense
end Silmaril.Semantics.Arena
