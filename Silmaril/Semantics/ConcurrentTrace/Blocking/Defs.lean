module

public import Silmaril.Semantics.ConcurrentTrace.Defs

/-! # Concurrent traces with blocking footprints

A footprint records an event's owner and the names whose events cannot swap
past it. The footprint constrains reorderings of a word. Each event is already
a single letter in that word.
-/

@[expose] public section

namespace Silmaril.Semantics.ConcurrentTrace.Blocking

universe u v u' v'

/-- Each event has one owner and a set of names whose events it blocks. -/
structure Footprint (Name : Type u) (Ev : Type v) where
  owner : Ev → Name
  blocks : Ev → Set Name

variable {Name : Type u} {Ev : Type v} {T : Type u} {E : Type v}
variable {T' : Type u'} {E' : Type v'}

/-- An adjacent swap is allowed when the owners differ and neither event blocks
the other's owner. The two membership tests account for both directions. -/
def Footprint.Independent (F : Footprint Name Ev) (a b : Ev) : Prop :=
  F.owner a ≠ F.owner b ∧ F.owner a ∉ F.blocks b ∧ F.owner b ∉ F.blocks a

/-- Words on the event alphabet modulo adjacent independent swaps. -/
abbrev Footprint.Trace (F : Footprint Name Ev) := TraceMonoid.Trace F.Independent

abbrev EventSyncLetter (Thread : Type u) (Payload : Type v) :=
  (Thread × Payload) ⊕ List Thread

/-- Ordinary events own their thread and have an empty blocking set. All syncs
share one reserved owner. Each blocks exactly the threads in its participant list. -/
def eventSync (T : Type u) (E : Type v) :
    Footprint (T ⊕ Unit) (EventSyncLetter T E) where
  owner
    | .inl (t, _) => .inl t
    | .inr _ => .inr ()
  blocks
    | .inl _ => ∅
    | .inr ts => {name | match name with
        | .inl t => t ∈ ts
        | .inr _ => False}

/-- The old and new letter types encode exactly the same labels. Sync labels
retain the whole list, with its order and duplicates. -/
def encodeLetter : Letter T E ≃ EventSyncLetter T E where
  toFun
    | .event t e => .inl (t, e)
    | .sync ts => .inr ts
  invFun
    | .inl (t, e) => .event t e
    | .inr ts => .sync ts
  left_inv a := by cases a <;> rfl
  right_inv := by rintro (⟨t, e⟩ | ts) <;> rfl

/-- Map a thread and payload in an ordinary event, and map a sync's participant list pointwise. -/
def mapEventSyncLetter (f : T → T') (g : E → E') : EventSyncLetter T E → EventSyncLetter T' E' :=
  Sum.map (Prod.map f g) (List.map f)

end Silmaril.Semantics.ConcurrentTrace.Blocking
