module

public import Silmaril.Semantics.ConcurrentTrace.Occurrences.Defs

/-! # Address conflict policies for concurrent occurrences -/

@[expose] public section

namespace Silmaril.Semantics.ConcurrentTrace.OccurrencePoset

universe u v a

/-- A policy assigns a set of conflicting addresses to an ordered pair of labels. -/
abbrev ConflictPolicy (T : Type u) (E : Type v) (Addr : Type a) :=
  Letter T E → Letter T E → Set Addr

variable {T : Type u} {E : Type v} {Addr : Type a}

/-- A footprint supplied for events, extended to syncs with an empty footprint. -/
def eventFootprint (footprint : T → E → Set Addr) : Letter T E → Set Addr
  | .event t e => footprint t e
  | .sync _ => ∅

/-- Any address touched by both events is a conflict under this policy. -/
def anyTouchPolicy (touches : T → E → Set Addr) : ConflictPolicy T E Addr :=
  fun l r => eventFootprint touches l ∩ eventFootprint touches r

/-- An address is a conflict when one event writes it and the other reads or writes it.
The first union branch includes write/write conflicts. -/
def readWritePolicy (reads writes : T → E → Set Addr) : ConflictPolicy T E Addr :=
  fun l r =>
    (eventFootprint writes l ∩ (eventFootprint reads r ∪ eventFootprint writes r)) ∪
      (eventFootprint writes r ∩ eventFootprint reads l)

/-- Apply a conflict policy to two distinct, causally incomparable occurrences. -/
def conflictAt (p : OccurrencePoset T E) (policy : ConflictPolicy T E Addr)
    (i j : Fin p.size) : Set Addr :=
  {a | p.Concurrent i j ∧ a ∈ policy (p.label i) (p.label j)}

/-- Collect the conflict addresses over all ordered pairs of concurrent occurrences. -/
def conflictAddresses (p : OccurrencePoset T E) (policy : ConflictPolicy T E Addr) : Set Addr :=
  {a | ∃ i j, a ∈ p.conflictAt policy i j}

end Silmaril.Semantics.ConcurrentTrace.OccurrencePoset
