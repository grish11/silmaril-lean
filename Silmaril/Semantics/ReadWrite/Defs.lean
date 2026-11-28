module

public import Init

/-! Chronological reads and writes over an arbitrary address, value and state type. -/

@[expose] public section
namespace Silmaril.Semantics.ReadWrite

universe u v w
variable {Address : Type u} {Value : Type v} {State : Type w}

/-- A read carries its observed value. A write carries the replacement value. -/
inductive Event (Address : Type u) (Value : Type v) where
  | read (address : Address) (value : Value)
  | write (address : Address) (value : Value)

abbrev Trace (Address : Type u) (Value : Type v) := List (Event Address Value)
abbrev ReadTrace (Address : Type u) (Value : Type v) := List (Address × Value)
abbrev WriteTrace (Address : Type u) (Value : Type v) := List (Address × Value)

/-- State operations needed by traces. A read leaves the state intact. A write
may fail. The backend determines which addresses can be read or written. -/
structure Access (Address : Type u) (Value : Type v) (State : Type w) where
  read : State → Address → Option Value
  write : State → Address → Value → Option State

/-- A successful write preserves the given observation at all other addresses.
Use the read operation as the observation when reasoning about read projections. -/
def Access.Frames {Observation : Type _} (access : Access Address Value State)
    (observe : State → Address → Observation) : Prop :=
  ∀ ⦃initial next address value other⦄, access.write initial address value = some next →
    other ≠ address → observe next other = observe initial other

namespace ReadTrace

def toTrace (reads : ReadTrace Address Value) : Trace Address Value :=
  reads.map fun (address, value) => .read address value

/-- All recorded values agree with one unchanged state. -/
def Agrees (reads : ReadTrace Address Value) (access : Access Address Value State)
    (state : State) : Prop :=
  ∀ entry ∈ reads, access.read state entry.1 = some entry.2

end ReadTrace

namespace WriteTrace

def toTrace (writes : WriteTrace Address Value) : Trace Address Value :=
  writes.map fun (address, value) => .write address value

end WriteTrace

namespace Trace

def reads (trace : Trace Address Value) : ReadTrace Address Value :=
  trace.filterMap fun
    | .read address value => some (address, value)
    | .write _ _ => none

def writes (trace : Trace Address Value) : WriteTrace Address Value :=
  trace.filterMap fun
    | .read _ _ => none
    | .write address value => some (address, value)

def ReadOnly (trace : Trace Address Value) : Prop := trace.reads.toTrace = trace

def WriteOnly (trace : Trace Address Value) : Prop := trace.writes.toTrace = trace

def Reads (trace : Trace Address Value) (address : Address) : Prop :=
  ∃ value, (address, value) ∈ trace.reads

/-- Addresses assigned at least once. -/
def Defs (trace : Trace Address Value) (address : Address) : Prop :=
  ∃ value, (address, value) ∈ trace.writes

/-- Addresses touched by any access, including reads of a value written earlier. -/
def Footprint (trace : Trace Address Value) (address : Address) : Prop := trace.Reads address ∨ trace.Defs address

/-- An address is used from the initial state if it is read before its first write.
An address can be in both the use and def sets. -/
def Uses : Trace Address Value → Address → Prop
  | [], _ => False
  | .read p _ :: rest, address => address = p ∨ Uses rest address
  | .write p _ :: rest, address => address ≠ p ∧ Uses rest address

/-- Replay relates the initial state to the state after the last event.
A read must match the state at its own position in the trace. -/
def Replays (access : Access Address Value State) : Trace Address Value → State → State → Prop
  | [], initial, final => initial = final
  | .read address value :: rest, initial, final =>
      access.read initial address = some value ∧ Replays access rest initial final
  | .write address value :: rest, initial, final =>
      ∃ next, access.write initial address value = some next ∧ Replays access rest next final

/-- Consistency with a specified initial state. -/
def Consistent (trace : Trace Address Value) (access : Access Address Value State)
    (initial : State) : Prop :=
  ∃ final, trace.Replays access initial final

/-- There is an initial state consistent with the trace. -/
def Satisfiable (trace : Trace Address Value) (access : Access Address Value State) : Prop :=
  ∃ initial, trace.Consistent access initial

/-- Both endpoints refine client-selected structure predicates. -/
def Validates (trace : Trace Address Value) (access : Access Address Value State)
    (before after : State → Prop) : Prop :=
  ∃ initial final, before initial ∧ trace.Replays access initial final ∧ after final

/-- The executable counterpart of replay when value equality is decidable. -/
def run [DecidableEq Value] (access : Access Address Value State) :
    Trace Address Value → State → Option State
  | [], initial => some initial
  | .read address value :: rest, initial =>
      if access.read initial address = some value then run access rest initial else none
  | .write address value :: rest, initial =>
      (access.write initial address value).bind (run access rest)

end Trace

end Silmaril.Semantics.ReadWrite
