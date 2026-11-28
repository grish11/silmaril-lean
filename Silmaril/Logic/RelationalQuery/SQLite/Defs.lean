module

public import Silmaril.Logic.RelationalQuery.Defs
public import Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Defs

/-! An interpretation of bound, admitted SQLite catalog point reads as Boolean queries. -/

@[expose] public section

namespace Silmaril.SQLite.Relational.CatalogExecutor

open Silmaril.Relational

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

/-- Retain the native typed cells, including the extra row identity slot. SQLite's cell
family depends on the schema, so the Lean cell types themselves serve as kind codes. -/
def querySchema (schema : TableSchema Affinity Expr) : QuerySchema Type :=
  ⟨Option schema.Index, schema.RowCell ValueModel.sqlValue ∘ schema.rowKind⟩

def queryCatalog (snapshot : SqlSnapshot sem) : QueryCatalog Type :=
  QueryCatalog.ofPacked snapshot.tables querySchema

def queryModel (snapshot : SqlSnapshot sem) : QueryCatalog.Model id (queryCatalog snapshot) :=
  QueryCatalog.modelOfPacked fun _ table => CheckedTable.rows table

/-- An admitted projection from `SELECT column FROM table WHERE rowid = ?1`.
Names use the existing resolver's spelling. The key is supplied when invoking the read. -/
structure PointRead (snapshot : SqlSnapshot sem) where
  table : Database.Support snapshot.tables
  columnName : String
  column : (QueryCatalog.entryAt snapshot.tables table).fst.Index
  found : (QueryCatalog.entryAt snapshot.tables table).fst.findColumn columnName = some column
  rowIdVisible : (QueryCatalog.entryAt snapshot.tables table).fst.resolvesRowId "rowid" = true
  ordinary : (QueryCatalog.entryAt snapshot.tables table).fst.generation column = none

namespace PointRead

variable {snapshot : SqlSnapshot sem}

/-- Read the same packed entry that gives the query catalog its component. -/
def target (read : PointRead snapshot) : Target sem :=
  let entry := QueryCatalog.entryAt snapshot.tables read.table
  ⟨entry.fst, read.column, entry.snd⟩

def invocation (read : PointRead snapshot) (key : Int64) : Invocation Names :=
  ⟨⟨⟨read.table.val, read.columnName⟩⟩, some (1, key)⟩

/-- The existing point-lookup observation, with its column label and optional cell. -/
def result (read : PointRead snapshot) (key : Int64) : SelectResult SqlValue :=
  ⟨read.target.schema.name read.column, read.target.lookup key⟩

/-- Observe whether the point read returns a row whose projected value passes a Lean test.
A constant true test observes row existence, including a row whose value is SQL NULL. -/
def sentence (read : PointRead snapshot) (key : Int64) (test : SqlValue → Bool) :
    DatabaseQuery.Sentence id (queryCatalog snapshot) :=
  .atom ⟨read.table, fun (row : TableRow ValueModel.sqlValue read.target.schema) =>
    row.rowId? == some key && test (row.get read.column)⟩

end PointRead

/-- The table part of a resolved SQLite catalog gives a signature independently of any rows. -/
def queryCatalogOfTables (catalog : TableCatalog Affinity Expr) : QueryCatalog Type :=
  QueryCatalog.ofCatalog catalog querySchema

/-- Read a snapshot's checked tables over a declared catalog with the same table schemas. -/
def tablesOver (snapshot : SqlSnapshot sem) {catalog : TableCatalog Affinity Expr}
    (compatible : snapshot.catalog.tables = catalog) :
    Database.Over catalog (CheckedTable ValueModel.sqlValue sem) :=
  fun name => congrFun compatible name ▸ (Database.Packed.unpack snapshot.tables).snd name

/-- The checked rows of a compatible snapshot, interpreted at the declared catalog signature. -/
def queryModelOfSnapshot (snapshot : SqlSnapshot sem) {catalog : TableCatalog Affinity Expr}
    (compatible : snapshot.catalog.tables = catalog) :
    QueryCatalog.Model id (queryCatalogOfTables catalog) :=
  QueryCatalog.modelOfOver (fun _ table => CheckedTable.rows table) (tablesOver snapshot compatible)

/-- A named point projection admitted by the declared table schemas. The selected table must
be present, with a visible `rowid` pseudocolumn and an ordinary projected column. -/
structure CatalogPointRead (catalog : TableCatalog Affinity Expr) where
  table : Database.Support catalog
  columnName : String
  column : (QueryCatalog.entryAt catalog table).Index
  found : (QueryCatalog.entryAt catalog table).findColumn columnName = some column
  rowIdVisible : (QueryCatalog.entryAt catalog table).resolvesRowId "rowid" = true
  ordinary : (QueryCatalog.entryAt catalog table).generation column = none

namespace CatalogPointRead

variable {catalog : TableCatalog Affinity Expr}

def schema (read : CatalogPointRead catalog) : TableSchema Affinity Expr :=
  QueryCatalog.entryAt catalog read.table

def invocation (read : CatalogPointRead catalog) (key : Int64) : Invocation Names :=
  ⟨⟨⟨read.table.val, read.columnName⟩⟩, some (1, key)⟩

/-- A bound rowid and projected-cell test at the declared catalog signature. -/
def sentence (read : CatalogPointRead catalog) (key : Int64) (test : SqlValue → Bool) :
    DatabaseQuery.Sentence id (queryCatalogOfTables catalog) :=
  .atom ⟨read.table, fun (row : TableRow ValueModel.sqlValue read.schema) =>
    row.rowId? == some key && test (row.get read.column)⟩

/-- Resolve the declared projection to the checked payload in a compatible snapshot. -/
def target (read : CatalogPointRead catalog) (snapshot : SqlSnapshot sem)
    (compatible : snapshot.catalog.tables = catalog) : Target sem :=
  ⟨read.schema, read.column,
    (tablesOver snapshot compatible).lookup read.table.val (Option.some_get _).symm⟩

def result (read : CatalogPointRead catalog) (snapshot : SqlSnapshot sem)
    (compatible : snapshot.catalog.tables = catalog) (key : Int64) : SelectResult SqlValue :=
  ⟨read.schema.name read.column, (read.target snapshot compatible).lookup key⟩

end CatalogPointRead
end Silmaril.SQLite.Relational.CatalogExecutor
