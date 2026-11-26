module

public import Silmaril.Semantics.SQLite.Relational.Catalog.Thms
public import Silmaril.Semantics.SQLite.Relational.Schema.SqlValue
public import Silmaril.Semantics.SQLite.Relational.Fragment.Defs

@[expose] public section

namespace Silmaril.SQLite.Relational.CatalogExecutor

open Silmaril.Relational (QueryRel)

variable {Expr : Type}

abbrev SqlSnapshot (sem : TableSemantics SqlValue Affinity Expr) :=
  Snapshot ValueModel.sqlValue sem

/-- Table and projection names in the normalized spelling used by the catalog. -/
structure Names where
  table : String
  column : String

inductive ResolveError where
  | missingTable (name : String)
  | missingColumn (table name : String)
  deriving DecidableEq, Repr

/-- An ordinal in the schema of the checked table selected by preparation. -/
structure Target (sem : TableSemantics SqlValue Affinity Expr) where
  schema : TableSchema Affinity Expr
  column : schema.Index
  table : CheckedTable ValueModel.sqlValue sem schema

/-- A pure snapshot has no additional file, cache, exchanges, or reader errors.
The shared statement executor still returns the catalog and session. -/
abbrev profile (sem : TableSemantics SqlValue Affinity Expr) : Profile where
  Value := SqlValue
  Catalog := SqlSnapshot sem
  Ref := Names
  Target := Target sem
  PrepareError := ResolveError
  ReadError := Empty
  Backing := Unit
  Cache := Unit
  Exchange := Empty

variable {sem : TableSemantics SqlValue Affinity Expr}

def resolve (snapshot : SqlSnapshot sem) (statement : Statement Names) :
    Except ResolveError (Plan (Target sem)) :=
  let names := statement.source
  match snapshot.tables names.table with
  | none => .error (.missingTable names.table)
  | some ⟨schema, table⟩ =>
    match schema.findColumn names.column with
    | none => .error (.missingColumn names.table names.column)
    | some column => .ok ⟨⟨schema, column, table⟩, schema.name column⟩

/-- Reject unsupported object and projection forms at the checked entry point.
Missing names in the admitted table profile continue to preparation. -/
def classify (snapshot : SqlSnapshot sem) (call : Invocation Names) : CheckedRequest Names :=
  let names := call.statement.source
  match snapshot.tables names.table with
  | none =>
    if (snapshot.objects.views names.table).isSome then .unsupported "view"
    else .invoke call
  | some ⟨schema, _⟩ =>
    if !schema.resolvesRowId "rowid" then .unsupported "rowid predicate"
    else if (schema.findColumn names.column).any (fun i => (schema.generation i).isSome) then
      .unsupported "generated projection"
    else .invoke call

def Target.lookup (target : Target sem) (key : Int64) : Option SqlValue :=
  (target.table.rows.find? (fun row => row.rowId? == some key)).map
    (fun row => row.get target.column)

/-- The relational lookup observes a matching row or absence of every match. -/
def Target.Matches (target : Target sem) (key : Int64) : Option SqlValue → Prop
  | none => ∀ row ∈ target.table.rows, row.rowId? ≠ some key
  | some value =>
    ∃ row ∈ target.table.rows, row.rowId? = some key ∧ row.get target.column = value

def readOutcome (cell : Option SqlValue) : ReadOutcome (profile sem) :=
  ⟨.ok cell, (), (), []⟩

/-- The evaluator for admitted calls. Use `execute` to apply catalog admission. -/
def executor (sem : TableSemantics SqlValue Affinity Expr) : Executor (profile sem) where
  resolve := resolve
  read _ query := readOutcome (query.1.lookup query.2)

def reference (sem : TableSemantics SqlValue Affinity Expr) : Reference (profile sem) where
  resolves := QueryRel.ofTotal resolve
  reads _ query out :=
    ∃ cell, query.1.Matches query.2 cell ∧ readOutcome cell = out

def execute (sem : TableSemantics SqlValue Affinity Expr) (db : Connection (profile sem))
    (call : Invocation Names) : CheckedOutcome (profile sem) :=
  (executor sem).check db (classify db.catalog call)

def denote (sem : TableSemantics SqlValue Affinity Expr) :
    QueryRel (Connection (profile sem)) (Invocation Names) (CheckedOutcome (profile sem)) :=
  fun db call => CheckedRequest.denote (reference sem).denote db (classify db.catalog call)

end Silmaril.SQLite.Relational.CatalogExecutor
