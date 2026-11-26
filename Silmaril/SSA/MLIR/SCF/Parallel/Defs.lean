module

public import Init.Data.List.FinRange
public import Init.Data.List.Perm

/-! Pure, one-dimensional reductions on unbounded natural indices. -/

@[expose] public section

namespace Silmaril.MLIR.SCF.Parallel

universe u v

/-- A mathematical natural-index slice of a positive-step, half-open iteration space.
Arithmetic on bounds and induction values is unbounded. -/
structure IndexSpace where
  lower : Nat
  upper : Nat
  step : Nat
  step_pos : 0 < step

/-- Ceiling of the positive distance divided by the step, with distance zero for empty spaces. -/
def IndexSpace.tripCount (space : IndexSpace) : Nat :=
  (space.upper - space.lower + (space.step - 1)) / space.step

abbrev IndexSpace.Trip (space : IndexSpace) := Fin space.tripCount

/-- The induction value for a trip ordinal. -/
def IndexSpace.index (space : IndexSpace) (trip : space.Trip) : Nat :=
  space.lower + trip.val * space.step

/-- The induction value just after the last trip, or the lower bound for an empty space. -/
def IndexSpace.exitIndex (space : IndexSpace) : Nat :=
  space.lower + space.tripCount * space.step

/-- Trip ordinals in increasing order. -/
def IndexSpace.trips (space : IndexSpace) : List space.Trip :=
  List.finRange space.tripCount

/-- An admissible enumeration visits each trip exactly once, in arbitrary order. -/
def IndexSpace.Enumeration (space : IndexSpace) :=
  {order : List space.Trip // order.Perm space.trips}

/-- Each leaf supplies the initial value or the contribution of a single trip. -/
inductive Input (space : IndexSpace) where
  | initial
  | trip (ordinal : space.Trip)

/-- A nonempty binary tree specifies the parenthesization of combiner calls. -/
inductive Tree (α : Type u) where
  | leaf (input : α)
  | fork (left right : Tree α)

def Tree.leaves {α : Type u} : Tree α → List α
  | .leaf input => [input]
  | .fork left right => left.leaves ++ right.leaves

def Tree.eval {α : Type u} {β : Type v} (value : α → β) (combine : β → β → β) :
    Tree α → β
  | .leaf input => value input
  | .fork left right => combine (left.eval value combine) (right.eval value combine)

/-- Add inputs to the right of a tree with successive left-associated combiner calls. -/
def Tree.appendLeaves {α : Type u} (tree : Tree α) (inputs : List α) : Tree α :=
  inputs.foldl (fun acc input => .fork acc (.leaf input)) tree

/-- The left-associated tree for a given ordered list of trips, starting with the initial value. -/
def IndexSpace.leftTree (space : IndexSpace) (order : List space.Trip) : Tree (Input space) :=
  (Tree.leaf Input.initial).appendLeaves (order.map Input.trip)

/-- The initial value is the first leaf and each trip occurs once. The binary shape is free. -/
def IndexSpace.Admissible (space : IndexSpace) (tree : Tree (Input space)) : Prop :=
  ∃ order : space.Enumeration, tree.leaves = Input.initial :: order.val.map Input.trip

/-- One typed reduction slot. Its binary combiner returns a value of the same type
as the initial value and each contribution. -/
structure Reduction (α : Type u) where
  initial : α
  contribution : Nat → α
  combine : α → α → α

def Reduction.value {α : Type u} (reduction : Reduction α) (space : IndexSpace) :
    Input space → α
  | .initial => reduction.initial
  | .trip ordinal => reduction.contribution (space.index ordinal)

/-- Evaluate a given tree. Admissibility is specified separately. -/
def Reduction.eval {α : Type u} (reduction : Reduction α) (space : IndexSpace)
    (tree : Tree (Input space)) : α :=
  tree.eval (reduction.value space) reduction.combine

/-- The possible result values of all admissible enumerations and trees. -/
def Reduction.Returns {α : Type u} (reduction : Reduction α) (space : IndexSpace)
    (result : α) : Prop :=
  ∃ tree, space.Admissible tree ∧ reduction.eval space tree = result

/-- A sequential left fold for a given order of the trips. -/
def Reduction.fold {α : Type u} (reduction : Reduction α) (space : IndexSpace)
    (order : List space.Trip) : α :=
  order.foldl (fun acc trip => reduction.combine acc (reduction.contribution (space.index trip)))
    reduction.initial

/-- The reference denotation fixes increasing trip order and left association. -/
def Reduction.denote {α : Type u} (reduction : Reduction α) (space : IndexSpace) : α :=
  reduction.fold space space.trips

/-- Finitely many reduction slots, each with its own carrier and typed combiner.
The grouped interpretation shares one trip enumeration and one tree between the slots. -/
structure GroupedReduction {n : Nat} (Carrier : Fin n → Type u) where
  initial : (slot : Fin n) → Carrier slot
  contribution : Nat → (slot : Fin n) → Carrier slot
  combine : (slot : Fin n) → Carrier slot → Carrier slot → Carrier slot

/-- Interpret a group as a reduction on the dependent product of the slot carriers. -/
def GroupedReduction.toReduction {n : Nat} {Carrier : Fin n → Type u}
    (group : GroupedReduction Carrier) : Reduction ((slot : Fin n) → Carrier slot) where
  initial := group.initial
  contribution := group.contribution
  combine left right slot := group.combine slot (left slot) (right slot)

end Silmaril.MLIR.SCF.Parallel
