module

public import Silmaril.Formats.PER.Fibers.Thms
public import Silmaril.Formats.PER.UnionFind.Defs

@[expose] public section

namespace Silmaril.Formats.PER.Parent

variable {Key : Type}

inductive Convention where
  | fixedPoint
  | terminalMissing
  deriving DecidableEq

def Terminal (mode : Convention) (parent : Key → Option Key) (key : Key) : Prop :=
  match mode with
  | .fixedPoint => parent key = some key
  | .terminalMissing => parent key = none

/-- A strict edge. Self loops are terminals in the fixed-point convention
and invalid in the terminal-missing convention. -/
def Step (parent : Key → Option Key) (key next : Key) : Prop :=
  parent key = some next ∧ key ≠ next

inductive Reaches (mode : Convention) (parent : Key → Option Key) : Key → Key → Prop where
  | stop {key : Key} : Terminal mode parent key → Reaches mode parent key key
  | next {key child root : Key} : Step parent key child → Reaches mode parent child root → Reaches mode parent key root

/-- All successful edges target successful keys, and strict parent descent
is well founded. In particular the eventual fixed point is a known key. -/
structure FixedForest (parent : Key → Option Key) : Prop where
  knownTarget : ∀ ⦃key next⦄, parent key = some next → (parent next).isSome
  terminates : WellFounded (fun next key => Step parent key next)

/-- Strict descent must terminate and cannot stop at a self-loop. The final
missing key is a distinct named endpoint, not one common failure value. -/
structure MissingForest (parent : Key → Option Key) : Prop where
  noFixed : ∀ key, parent key ≠ some key
  terminates : WellFounded (fun next key => Step parent key next)

def Roots (mode : Convention) (parent : Key → Option Key) : EncRel Key Key :=
  fun key root => (parent key).isSome ∧ Reaches mode parent key root

def partition (mode : Convention) (parent : Key → Option Key) : PER Key := PER.ofRelation (Roots mode parent)

/-- Connectivity is reflexive only at endpoints of actual edges. This graph
interpretation handles cycles (including loops) without claiming find terminates. -/
def incident (parent : Key → Option Key) (key : Key) : Prop :=
  (parent key).isSome ∨ ∃ source, parent source = some key

def connectivity (parent : Key → Option Key) : PER Key :=
  (⟨Relation.EqvGen (fun key next => parent key = some next),
    ⟨fun _ _ h => .symm _ _ h, fun _ _ _ h k => .trans _ _ _ h k⟩⟩ : PER Key).restrict (incident parent)

end Silmaril.Formats.PER.Parent
