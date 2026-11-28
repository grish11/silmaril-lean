module

public import Silmaril.Semantics.ReadWrite.Defs
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Order.BooleanAlgebra.Set

/-! Observations of chronological access traces at progressively less detail. -/

@[expose] public section
namespace Silmaril.Semantics.ReadWrite

universe u v
variable {Address : Type u} {Value : Type v}

/-- An access with its value erased. Both the kind and the address are visible. -/
inductive AddressEvent (Address : Type u) where
  | read (address : Address)
  | write (address : Address)
  deriving DecidableEq

abbrev AddressTrace (Address : Type u) := List (AddressEvent Address)

def Event.eraseValue : Event Address Value → AddressEvent Address
  | .read address _ => .read address
  | .write address _ => .write address

def Trace.eraseValues (trace : Trace Address Value) : AddressTrace Address :=
  trace.map Event.eraseValue

def AddressTrace.reads (trace : AddressTrace Address) : List Address :=
  trace.filterMap fun
    | .read address => some address
    | .write _ => none

def AddressTrace.writes (trace : AddressTrace Address) : List Address :=
  trace.filterMap fun
    | .read _ => none
    | .write address => some address

/-- A single address set with union as multiplication and the empty set as unit. -/
@[ext] structure AddressSet (Address : Type u) where
  addresses : Set Address

instance : CommMonoid (AddressSet Address) where
  one := ⟨∅⟩
  mul first last := ⟨first.addresses ∪ last.addresses⟩
  one_mul _ := AddressSet.ext (Set.empty_union _)
  mul_one _ := AddressSet.ext (Set.union_empty _)
  mul_assoc _ _ _ := AddressSet.ext (Set.union_assoc _ _ _)
  mul_comm _ _ := AddressSet.ext (Set.union_comm _ _)

/-- All addresses read and all addresses written, independent of order or multiplicity. -/
@[ext] structure AccessSets (Address : Type u) where
  reads : Set Address
  writes : Set Address

instance : CommMonoid (AccessSets Address) where
  one := ⟨∅, ∅⟩
  mul first last := ⟨first.reads ∪ last.reads, first.writes ∪ last.writes⟩
  one_mul _ := AccessSets.ext (Set.empty_union _) (Set.empty_union _)
  mul_one _ := AccessSets.ext (Set.union_empty _) (Set.union_empty _)
  mul_assoc _ _ _ := AccessSets.ext (Set.union_assoc _ _ _) (Set.union_assoc _ _ _)
  mul_comm _ _ := AccessSets.ext (Set.union_comm _ _) (Set.union_comm _ _)

def AccessSets.defs (sets : AccessSets Address) : Set Address := sets.writes

def AccessSets.footprint (sets : AccessSets Address) : Set Address := sets.reads ∪ sets.writes

/-- Initial uses (reads before the first write to the same address) and all definitions.
The product is chronological: definitions in the first segment supply later reads. -/
@[ext] structure UseDef (Address : Type u) where
  uses : Set Address
  defs : Set Address

instance : Monoid (UseDef Address) where
  one := ⟨∅, ∅⟩
  mul first last := ⟨first.uses ∪ (last.uses \ first.defs), first.defs ∪ last.defs⟩
  one_mul first := UseDef.ext
    (show ∅ ∪ (first.uses \ ∅) = first.uses by rw [Set.empty_union, Set.sdiff_empty]) (Set.empty_union _)
  mul_one first := UseDef.ext
    (show first.uses ∪ (∅ \ first.defs) = first.uses by rw [Set.empty_sdiff, Set.union_empty])
    (Set.union_empty _)
  mul_assoc first middle last := by
    refine UseDef.ext ?_ (Set.union_assoc _ _ _)
    change (first.uses ∪ (middle.uses \ first.defs)) ∪ (last.uses \ (first.defs ∪ middle.defs)) =
      first.uses ∪ ((middle.uses ∪ (last.uses \ middle.defs)) \ first.defs)
    rw [Set.union_sdiff_distrib, Set.sdiff_sdiff, Set.union_comm middle.defs, Set.union_assoc]

/-- Every access either uses the initial value or touches an address in the def set. -/
def UseDef.footprint (summary : UseDef Address) : Set Address := summary.uses ∪ summary.defs

def Trace.accessSets (trace : Trace Address Value) : AccessSets Address :=
  ⟨{address | trace.Reads address}, {address | trace.Defs address}⟩

def Trace.useDef (trace : Trace Address Value) : UseDef Address :=
  ⟨{address | trace.Uses address}, {address | trace.Defs address}⟩

def AddressTrace.accessSets (trace : AddressTrace Address) : AccessSets Address :=
  ⟨{address | address ∈ trace.reads}, {address | address ∈ trace.writes}⟩

/-- Interpret a single access as a use/def summary. -/
def AddressEvent.useDef : AddressEvent Address → UseDef Address
  | .read address => ⟨{address}, ∅⟩
  | .write address => ⟨∅, {address}⟩

def AddressTrace.useDef (trace : AddressTrace Address) : UseDef Address :=
  FreeMonoid.lift AddressEvent.useDef (FreeMonoid.ofList trace)

end Silmaril.Semantics.ReadWrite
