module

public import Silmaril.Formats.PER.Dense.Thms
public import Silmaril.Formats.PER.Parent.Thms

@[expose] public section

namespace Silmaril.Formats.PER.Dense

variable {Code Carrier : Type} {Row : Nat → Type}

inductive Observation (Target : Type) where
  | unknown
  | missing
  | invalid (address : Nat)
  | edge (target : Target)
  deriving DecidableEq, Repr

def Observation.target? : Observation Carrier → Option Carrier
  | .edge target => some target
  | _ => none

/-- The row decoder specifies the sentinel convention. A successful address
has not yet passed the table-bound check. -/
structure Pointers (Row : Nat → Type) where
  table : Table Row
  address : Row table.size → Option Nat

def Pointers.ofList (index : Index Code) (rows : List Code) : Pointers (fun _ => Code) :=
  ⟨Table.ofList rows, some ∘ index.toNat⟩

def Pointers.ofOptional (index : Index Code) (rows : List (Option Code)) : Pointers (fun _ => Option Code) :=
  ⟨Table.ofList rows, fun row => row.map index.toNat⟩

/-- The specified code, and only that code, means no outgoing edge. Choose
a code outside the table's index range if every row should remain addressable. -/
def Pointers.ofSentinel (index : Index Code) (sentinel : Nat) (rows : List Code) : Pointers (fun _ => Code) :=
  ⟨Table.ofList rows, fun row => if index.toNat row = sentinel then none else some (index.toNat row)⟩

def Pointers.ofFin (table : Table (fun size => Option (Fin size))) : Pointers (fun size => Option (Fin size)) :=
  ⟨table, fun row => row.map Fin.val⟩

def Pointers.ofFinTotal (table : Table Fin) : Pointers Fin := ⟨table, some ∘ Fin.val⟩

def Pointers.observe (raw : Pointers Row) (source : Nat) : Observation (Fin raw.table.size) :=
  match raw.table.read? source with
  | none => .unknown
  | some row => match raw.address row with
    | none => .missing
    | some address => if bound : address < raw.table.size then .edge ⟨address, bound⟩ else .invalid address

abbrev Pointers.Valid (raw : Pointers Row) : Prop :=
  (raw.table.rows.all fun row => (raw.address row).all fun target => decide (target < raw.table.size)) = true

/-- Range checking does not certify termination, acyclicity, rootedness or
canonical labels. Those are distinct semantic conditions. -/
def Pointers.Checked (Row : Nat → Type) := {raw : Pointers Row // raw.Valid}

def Pointers.check? (raw : Pointers Row) : Option (Checked Row) :=
  if valid : raw.Valid then some ⟨raw, valid⟩ else none

def Pointers.Checked.parent (checked : Checked Row) (key : Fin checked.val.table.size) :
    Option (Fin checked.val.table.size) := (checked.val.observe key.val).target?

inductive ParentView where
  | direct
  | fixedPoint
  | terminalMissing
  | connectivity

/-- Positive reachability in the selected convention. Without the relevant
forest invariant, the path interpretations can have smaller support. -/
def Pointers.Checked.per (checked : Checked Row) (view : ParentView) : PER (Fin checked.val.table.size) :=
  match view with
  | .direct => fibers checked.parent
  | .fixedPoint => Parent.partition .fixedPoint checked.parent
  | .terminalMissing => Parent.partition .terminalMissing checked.parent
  | .connectivity => Parent.connectivity checked.parent

def Pointers.strategy (view : ParentView) (index : Index Carrier) : Strategy (Checked Row) Carrier :=
  ⟨fun checked => onIndex (checked.per view) index⟩

def Strategy.unionFind [LinearOrder Carrier] : Strategy (UnionFind Carrier) Carrier := ⟨UnionFind.partition⟩

/-- A caller-supplied decision procedure allows canonical representatives of
the selected finite relation; this is not a traversal algorithm. -/
def Pointers.Checked.normalize (checked : Checked Row) (view : ParentView) [DecidableRel (checked.per view).rel] :
    Silmaril.Semantics.OrderedMap (Fin checked.val.table.size) (Fin checked.val.table.size) :=
  Partition.canonicalOn Finset.univ (checked.per view)

end Silmaril.Formats.PER.Dense
