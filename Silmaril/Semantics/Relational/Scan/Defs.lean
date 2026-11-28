module

public import Silmaril.Semantics.Relational.Table.Organization.Defs

/-! Ordered observations and pure scans over nullable relational tables. -/

@[expose] public section

namespace Silmaril.Relational.Scan

/-- Each position carries a caller-supplied column identity and a type code.
Identities can carry schema metadata. Projection addresses positions and copies their labels. -/
abbrev Schema (Id Kind : Type*) := PositionalSchema (Id × Kind)

/-- `none` denotes null. Every present cell has the value type of its column. -/
abbrev Row {Id Kind : Type*} (schema : Schema Id Kind) (Value : Kind → Type*) :=
  Relational.Row (Prod.snd ∘ schema.kind) (fun kind => Option (Value kind))

abbrev Table {Id Kind : Type*} (schema : Schema Id Kind) (Value : Kind → Type*) :=
  Relational.Table (Prod.snd ∘ schema.kind) (fun kind => Option (Value kind))

abbrev Columns {Id Kind : Type*} (schema : Schema Id Kind) (Value : Kind → Type*) :=
  AlignedColumns (Prod.snd ∘ schema.kind) (fun kind => Option (Value kind))

/-- The schema and ordered typed rows are both observed. Equal rows may occupy
distinct positions, including when the schema has zero columns. -/
structure Observation (Id : Type*) {Kind : Type*} (Value : Kind → Type*) where
  schema : Schema Id Kind
  rows : Table schema Value

variable {Id Kind : Type*} {Value : Kind → Type*} {source : Schema Id Kind}

def Observation.rowCount (observation : Observation Id Value) : Nat := observation.rows.length

def Observation.ofColumns (schema : Schema Id Kind) (columns : Columns schema Value) :
    Observation Id Value :=
  ⟨schema, columns.toRows⟩

/-- Each output position selects a valid input position. Reordering and repetition
are permitted, as is selecting zero columns. -/
structure Projection (source : Schema Id Kind) where
  width : Nat
  index : Fin width → Fin source.width

namespace Projection

/-- Construct a projection from a runtime array of checked input positions. -/
def ofArray (indices : Array (Fin source.width)) : Projection source :=
  ⟨indices.size, fun i => indices[i]⟩

def schema (p : Projection source) : Schema Id Kind := ⟨p.width, source.kind ∘ p.index⟩

def columnMap (p : Projection source) : ColumnMap p.schema.kind source.kind :=
  ⟨p.index, fun _ => rfl⟩

def id (schema : Schema Id Kind) : Projection schema := ⟨schema.width, fun i => i⟩

/-- First project by `p`, then by `q`. -/
def comp (p : Projection source) (q : Projection p.schema) : Projection source :=
  ⟨q.width, p.index ∘ q.index⟩

def projectRow (p : Projection source) (row : Row source Value) : Row p.schema Value :=
  p.columnMap.pullRow Prod.snd row

def project (p : Projection source) (rows : Table source Value) : Table p.schema Value :=
  rows.map p.projectRow

/-- Select columns directly, preserving the explicit input row count. -/
def projectColumns (p : Projection source) (columns : Columns source Value) :
    Columns p.schema Value where
  rowCount := columns.rowCount
  values i := columns.values (p.index i)
  length_eq i := columns.length_eq (p.index i)

end Projection

/-- A total predicate returns true, false, or `none` (unknown). This interface
has no predicate error outcome. -/
abbrev Predicate (schema : Schema Id Kind) (Value : Kind → Type*) := Row schema Value → Option Bool

/-- Keep true rows in input order. False and unknown both discard the row. -/
def select (predicate : Predicate source Value) (rows : Table source Value) : Table source Value :=
  rows.filter fun row => (predicate row).getD false

/-- Evaluate the predicate on the full input row before projecting output columns. -/
def Projection.scan (p : Projection source) (predicate : Predicate source Value)
    (rows : Table source Value) : Table p.schema Value :=
  p.project (select predicate rows)

end Silmaril.Relational.Scan
