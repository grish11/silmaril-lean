module

public import Silmaril.Formats.PER.Fibers.Thms
public import Silmaril.Semantics.OrderedMap.Finite.Thms

@[expose] public section

namespace Silmaril.Formats.PER.Dense

open Silmaril.Semantics

variable {Carrier Source Key Label : Type} {Row : Nat → Type}

/-- A checked conversion, not modular truncation. A carrier may represent
only some natural numbers. No global index instance is installed. -/
structure Index (Carrier : Type) where
  toNat : Carrier → Nat
  ofNat? : Nat → Option Carrier
  read_write : ∀ value, ofNat? (toNat value) = some value
  write_read : ∀ ⦃number value⦄, ofNat? number = some value → toNat value = number

def Index.nat : Index Nat := ⟨id, some, fun _ => rfl, by
  intro number value hit
  exact (Option.some.inj hit).symm⟩

def Index.fin (capacity : Nat) : Index (Fin capacity) where
  toNat := Fin.val
  ofNat? number := if bound : number < capacity then some ⟨number, bound⟩ else none
  read_write value := by simp [value.isLt]
  write_read := by
    intro number value hit
    split at hit
    · exact (congrArg Fin.val (Option.some.inj hit)).symm
    · cases hit

def Index.viaEquiv (index : Index Carrier) (equiv : Key ≃ Carrier) : Index Key where
  toNat := index.toNat ∘ equiv
  ofNat? number := (index.ofNat? number).map equiv.symm
  read_write value := by simp [index.read_write]
  write_read := by
    intro number value hit
    obtain ⟨decoded, read, equal⟩ := Option.map_eq_some_iff.mp hit
    have packed : equiv value = decoded := by rw [← equal, equiv.apply_symm_apply]
    exact (congrArg index.toNat packed).trans (index.write_read read)

def Index.uint32 : Index UInt32 := (Index.fin UInt32.size).viaEquiv
  ⟨UInt32.toFin, UInt32.ofFin, UInt32.ofFin_toFin, UInt32.toFin_ofFin⟩

def Index.uint64 : Index UInt64 := (Index.fin UInt64.size).viaEquiv
  ⟨UInt64.toFin, UInt64.ofFin, UInt64.ofFin_toFin, UInt64.toFin_ofFin⟩

/-- Here `none` is an actual carrier value and occupies row zero. This is
independent of an outer `Option` indicating absence of a classification. -/
def optionNatEquiv : Option Nat ≃ Nat where
  toFun := fun value => value.elim 0 Nat.succ
  invFun := fun number => match number with | 0 => none | number + 1 => some number
  left_inv := by intro value; cases value <;> rfl
  right_inv := by intro number; cases number <;> rfl

def Index.optionNat : Index (Option Nat) := Index.nat.viaEquiv optionNatEquiv

def Index.toFin? (index : Index Carrier) (size : Nat) (value : Carrier) : Option (Fin size) :=
  (Index.fin size).ofNat? (index.toNat value)

def Index.fromFin? (index : Index Carrier) {size : Nat} (key : Fin size) : Option Carrier := index.ofNat? key.val

/-- Fix the size before choosing the row type. In particular rows may hold
`Fin size` indices without a self-dependent list-length expression. -/
structure Table (Row : Nat → Type) where
  size : Nat
  rows : List (Row size)
  length_eq : rows.length = size

def Table.ofList (rows : List Label) : Table (fun _ => Label) := ⟨rows.length, rows, rfl⟩

def Table.read? (table : Table Row) (key : Nat) : Option (Row table.size) := table.rows[key]?

def Table.at (table : Table Row) (key : Fin table.size) : Row table.size :=
  table.rows[key.val]'(table.length_eq.symm ▸ key.isLt)

def Table.readIndex? (table : Table Row) (index : Index Carrier) (key : Carrier) : Option (Row table.size) :=
  table.read? (index.toNat key)

/-- Direct fibers work with any label type. Neither labels nor rows are
interpreted as indices unless the caller explicitly chooses a pointer view. -/
def Table.labelPER (table : Table Row) (index : Index Carrier) (label : Row table.size → Option Label) : PER Carrier :=
  fibers fun key => (table.readIndex? index key).bind label

/-- Reuse the finite-map representation and its codecs. For option-valued
rows, stored `none` stays a value rather than disappearing from the map. -/
def Table.toMap (table : Table Row) : OrderedMap Nat (Row table.size) :=
  OrderedMap.ofLookupOn (Finset.range table.size) table.read?

/-- A first-class interpretation, allowing several meanings of the same
table without competing instances. Its total view is derived, not supplied. -/
structure Strategy (Source Key : Type) where
  per : Source → PER Key

def Strategy.ofLabels (lookup : Source → Key → Option Label) : Strategy Source Key := ⟨fun source => fibers (lookup source)⟩

def Strategy.ofSetoid (model : Source → Setoid Key) : Strategy Source Key :=
  ⟨fun source => ⟨(model source).r, ⟨fun _ _ => (model source).iseqv.symm, fun _ _ _ => (model source).iseqv.trans⟩⟩⟩

def Strategy.direct : Strategy (List Label) Nat :=
  ⟨fun rows => (Table.ofList rows).labelPER Index.nat some⟩

def Strategy.directOptional : Strategy (List (Option Label)) Nat :=
  ⟨fun rows => (Table.ofList rows).labelPER Index.nat id⟩

/-- Reflexive completion adds a singleton for each unsupported key. It
neither makes all unknown keys equivalent nor makes any of them supported. -/
def completion (partition : PER Key) : Setoid Key where
  r left right := left = right ∨ partition.rel left right
  iseqv := ⟨fun _ => .inl rfl, fun hit => hit.elim (fun equal => .inl equal.symm) (fun edge => .inr (partition.laws.symm edge)), by
    intro left mid right first second
    rcases first with rfl | first
    · exact second
    · rcases second with rfl | second
      · exact .inr first
      · exact .inr (partition.laws.trans first second)⟩

def Strategy.total (strategy : Strategy Source Key) (source : Source) : Setoid Key := completion (strategy.per source)

/-- Two stages: classify an ambient key, then compare its successful
carrier values. Outer `none` never becomes a carrier class. -/
def Strategy.pull (strategy : Strategy Source Carrier) (classify : Key → Option Carrier) : Strategy Source Key :=
  ⟨fun source => (strategy.per source).decodePull classify⟩

def onIndex {size : Nat} (relation : PER (Fin size)) (index : Index Carrier) : PER Carrier :=
  relation.decodePull (index.toFin? size)

end Silmaril.Formats.PER.Dense
