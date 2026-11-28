module

public import Silmaril.Semantics.Relational.Database.Thms
public import Mathlib.Logic.Equiv.Option
public import Silmaril.Semantics.SQLite.Relational.Table.Thms

/-! Track C databases of SQLite tables, catalog metadata and snapshot foreign-key checks. -/

@[expose] public section

namespace Silmaril.SQLite.Relational

open Silmaril.Relational (Constrained)
open Silmaril.Relational.Database (Partial)

abbrev TableCatalog (Affinity Expr : Type) :=
  Silmaril.Relational.Database.Catalog String (TableSchema Affinity Expr)

abbrev PackedDatabase {Value Affinity Expr : Type}
    (model : ValueModel Value Affinity) (sem : TableSemantics Value Affinity Expr) :=
  Silmaril.Relational.Database.Packed String (CheckedTable model sem)

abbrev PackedColumnDatabase {Value Affinity Expr : Type}
    (model : ValueModel Value Affinity) (sem : TableSemantics Value Affinity Expr) :=
  Silmaril.Relational.Database.Packed String (CheckedColumns model sem)

/-- Transpose all present checked tables, retaining their schema and name. -/
def packedRowsEquivColumns {Value Affinity Expr : Type}
    {model : ValueModel Value Affinity} {sem : TableSemantics Value Affinity Expr} :
    PackedDatabase model sem ≃ PackedColumnDatabase model sem :=
  Equiv.piCongrRight fun _ => (Equiv.sigmaCongrRight fun _ => CheckedTable.rowsEquivColumns).optionCongr

abbrev DependentDatabase {Value Affinity Expr : Type}
    (model : ValueModel Value Affinity) (sem : TableSemantics Value Affinity Expr) :=
  Silmaril.Relational.Database.Dependent String (CheckedTable model sem)

inductive IndexTerm (Expr : Type) where
  | column (name : String)
  | expression (expression : Expr)

structure IndexColumn (Expr : Type) where
  term : IndexTerm Expr
  collation : Option String := none
  descending : Bool := false

structure IndexDecl (Expr : Type) where
  table : String
  columns : List (IndexColumn Expr)
  unique : Bool := false
  predicate : Option Expr := none

structure ViewDecl (Expr : Type) where
  columns : List String
  definition : Expr

inductive TriggerTiming where
  | before
  | after
  | insteadOf
  deriving DecidableEq, Repr

inductive TriggerEvent where
  | insert
  | update (ofColumns : List String)
  | delete
  deriving DecidableEq, Repr

structure TriggerDecl (Expr : Type) where
  target : String
  timing : TriggerTiming
  event : TriggerEvent
  guard : Option Expr := none
  body : List Expr

/-- Metadata identifying a registered collation. The execution profile supplies comparisons. -/
structure CollationDecl where
  implementation : String

inductive FunctionArity where
  | fixed (count : Nat)
  | variadic
  deriving DecidableEq, Repr

inductive FunctionKind where
  | scalar
  | aggregate
  | window
  deriving DecidableEq, Repr

structure FunctionDecl where
  implementation : String
  kind : FunctionKind
  deterministic : Bool := false

/-- Resolved declarations. Function and collation registrations are
connection-side metadata. The other declarations describe schema objects. -/
structure CatalogObjects (Expr : Type) where
  indices : Partial String (IndexDecl Expr) := fun _ => none
  views : Partial String (ViewDecl Expr) := fun _ => none
  triggers : Partial String (TriggerDecl Expr) := fun _ => none
  collations : Partial String CollationDecl := fun _ => none
  functions : Partial (String × FunctionArity) FunctionDecl := fun _ => none

structure Catalog (Affinity Expr : Type) where
  tables : TableCatalog Affinity Expr
  objects : CatalogObjects Expr

def Catalog.findColumn {Affinity Expr : Type} (catalog : Catalog Affinity Expr)
    (tableName columnName : String) : Option (Σ schema : TableSchema Affinity Expr, schema.Index) := do
  let schema ← catalog.tables tableName
  let index ← schema.findColumn columnName
  return ⟨schema, index⟩

variable {Value Affinity Expr : Type}
variable {model : ValueModel Value Affinity} {sem : TableSemantics Value Affinity Expr}

/-- A snapshot holds checked tables and the declarations visible to the caller. -/
structure Snapshot (model : ValueModel Value Affinity) (sem : TableSemantics Value Affinity Expr) where
  tables : PackedDatabase model sem
  objects : CatalogObjects Expr

def Snapshot.catalog (snapshot : Snapshot model sem) : Catalog Affinity Expr :=
  ⟨Silmaril.Relational.Database.Packed.catalog snapshot.tables, snapshot.objects⟩

namespace ForeignKey

/-- Resolve an explicit parent key in order, restricted to declared PRIMARY KEY
and table UNIQUE constraints. The return value pairs each child position with
its corresponding parent position. -/
def resolveParent {child : Type} (key : ForeignKey child) (parent : TableSchema Affinity Expr) :
    Option (List (child × parent.Index)) := do
  let cols ← key.parentColumns.columns.mapM parent.findColumn
  let childCols := key.child.columns
  let declared := parent.primaryKey.any (fun pk => pk.columns == cols) ||
    parent.uniqueKeys.any (fun uk => uk.columns == cols)
  if declared && childCols.length == cols.length then some (childCols.zip cols) else none

/-- Snapshot validation for immediate foreign keys. A NULL anywhere in a
child key satisfies the row check. Otherwise there must be a matching parent
row using the comparison for the parent column's declaration and collation. -/
def holds (db : PackedDatabase model sem) {child : TableSchema Affinity Expr}
    (table : CheckedTable model sem child) (key : ForeignKey child.Index) : Bool :=
  match db key.parentTable with
  | none => false
  | some ⟨parent, parentTable⟩ =>
    match key.resolveParent parent with
    | none => false
    | some pairs =>
      table.rows.all fun row =>
        (pairs.any fun p => model.isNull (row.get p.1)) ||
          (parentTable.rows.any fun parentRow =>
            pairs.all fun (childCol, parentCol) =>
              let value := parentRow.get parentCol
              !model.isNull value &&
                sem.foreignEqual (parent.kind parentCol) (parent.column parentCol).collation
                  (row.get childCol) value)

end ForeignKey

def Snapshot.ForeignKeysValid (snapshot : Snapshot model sem) : Prop :=
  ∀ name schema table, snapshot.tables name = some ⟨schema, table⟩ →
    schema.foreignKeys.all (fun key => key.holds snapshot.tables table) = true

abbrev CheckedSnapshot (model : ValueModel Value Affinity) (sem : TableSemantics Value Affinity Expr) :=
  Constrained (Snapshot model sem) Snapshot.ForeignKeysValid

abbrev RowsDatabase (Value : Type) :=
  Silmaril.Relational.Database.Dynamic String (List (List Value))

/-- Erase table schemas, row identities and certificates, preserving each
name's presence and the order of its rows and cells. -/
def eraseDatabase (db : PackedDatabase model sem) : RowsDatabase Value :=
  Silmaril.Relational.Database.Packed.erase (fun _ table => table.values) db

/-- Retain the schema and row identities alongside the observable cell values. -/
def encodeTable (schema : TableSchema Affinity Expr) (table : CheckedTable model sem schema) :
    Σ schema : TableSchema Affinity Expr, List (schema.RowId × List Value) :=
  ⟨schema, table.rows.map TableRow.withValues⟩

abbrev IdentifiedRowsDatabase (Affinity Expr Value : Type) :=
  Silmaril.Relational.Database.Dynamic String
    (Σ schema : TableSchema Affinity Expr, List (schema.RowId × List Value))

def eraseKeepingIdentity (db : PackedDatabase model sem) : IdentifiedRowsDatabase Affinity Expr Value :=
  Silmaril.Relational.Database.Packed.erase encodeTable db

end Silmaril.SQLite.Relational
