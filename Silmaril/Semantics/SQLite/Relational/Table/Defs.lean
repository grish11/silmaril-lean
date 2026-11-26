module

public import Silmaril.Semantics.SQLite.Relational.Schema.Defs

/-! Typed table snapshots, bounded generation and logical table checks. -/

@[expose] public section

namespace Silmaril.SQLite.Relational

open Silmaril.Relational (AlignedColumns Constrained GeneratedColumns)

inductive CheckTruth where
  | false
  | true
  | null
  deriving DecidableEq, Repr

/-- Callers interpret resolved expressions and key comparisons. A missing
expression result denotes failure. Key comparisons receive the column's
declared type and collation, with NULL handling performed by the caller of the
comparison. -/
structure TableSemantics (Value Affinity Expr : Type) where
  evalGenerated : Expr → List Value → Option Value
  evalCheck : {width : Nat} → Expr → (Fin width → Value) → Option CheckTruth
  keyEqual : {mode : TypingMode} → DeclaredColumnType Affinity mode → Option String → Value → Value → Bool
  foreignEqual : {mode : TypingMode} → DeclaredColumnType Affinity mode →
    Option String → (child parent : Value) → Bool

namespace TableSchema

variable {Value Affinity Expr : Type} (schema : TableSchema Affinity Expr)

def rowKind (axis : Option schema.Index) : Option (DeclaredColumnType Affinity schema.mode) :=
  axis.map schema.kind

/-- The alignment axis includes a row identity slot. In WITHOUT ROWID tables
the slot has a single inhabitant and contributes no observable rowid. -/
def RowCell (model : ValueModel Value Affinity) : Option (DeclaredColumnType Affinity schema.mode) → Type
  | none => schema.RowId
  | some type => type.Cell model

abbrev Cells (model : ValueModel Value Affinity) :=
  Silmaril.Relational.Row schema.kind (DeclaredColumnType.Cell model)

abbrev SuppliedCells (model : ValueModel Value Affinity) :=
  Silmaril.Relational.Row (fun i : schema.Supplied => schema.kind i.val) (DeclaredColumnType.Cell model)

end TableSchema

variable {Value Affinity Expr : Type}

abbrev TableRow (model : ValueModel Value Affinity) (schema : TableSchema Affinity Expr) :=
  Silmaril.Relational.Row schema.rowKind (schema.RowCell model)

namespace TableRow

variable {model : ValueModel Value Affinity} {schema : TableSchema Affinity Expr}

def ofCells (id : schema.RowId) (cells : schema.Cells model) : TableRow model schema
  | none => id
  | some i => cells i

def rowId (row : TableRow model schema) : schema.RowId := row none

def rowId? (row : TableRow model schema) : Option Int64 := schema.rowId? row.rowId

def cell (row : TableRow model schema) (i : schema.Index) : (schema.kind i).Cell model := row (some i)

def get (row : TableRow model schema) (i : schema.Index) : Value := (row.cell i).val

def withValues (row : TableRow model schema) : schema.RowId × List Value :=
  (row.rowId, List.ofFn row.get)

end TableRow

namespace TableSchema

variable (schema : TableSchema Affinity Expr) (model : ValueModel Value Affinity)
variable (sem : TableSemantics Value Affinity Expr)

/-- Track C generation instantiated with possibly failing, storage-typed cells.
The evaluator receives values in the resolved dependency order. -/
def generatedColumns :
    GeneratedColumns (fun i : schema.Supplied => schema.kind i.val)
      (fun i : schema.Generated => schema.kind i.val.1)
      (fun type => Option (type.Cell model)) where
  Dependency j := Fin j.val.2.inputs.length
  input j d := ⟨j.val.2.inputs.get d,
    schema.inputsSupplied j.val.1 j.val.2 j.property _ (List.get_mem _ _)⟩
  eval j inputs := do
    let values ← (List.ofFn (fun d => (inputs d).map Subtype.val)).mapM id
    let result ← sem.evalGenerated j.val.2.expression values
    (schema.kind j.val.1).store model result

def fill (supplied : schema.SuppliedCells model) (i : schema.Index) :
    Option ((schema.kind i).Cell model) :=
  match h : schema.generation i with
  | none => some (supplied ⟨i, h⟩)
  | some spec => (schema.generatedColumns model sem).evaluate (fun j => some (supplied j))
      ⟨(i, spec), h⟩

/-- Materialize the single generation layer. Failure in any derived cell
rejects the complete row. Local and whole-table constraints are checked separately. -/
def materialize (supplied : schema.SuppliedCells model) : Option (schema.Cells model) :=
  if success : ∀ i, (schema.fill model sem supplied i).isSome = true then
    some (fun i => (schema.fill model sem supplied i).get (success i))
  else none

def GenerationValid (cells : schema.Cells model) : Prop :=
  ∀ i, schema.fill model sem (fun j => cells j.val) i = some (cells i)

def rowChecks (row : TableRow model schema) : Bool :=
  (List.finRange schema.width).all (fun i => !(schema.column i).notNull || !model.isNull (row.get i)) &&
  (schema.checks.all fun expr =>
    match sem.evalCheck expr row.get with
    | some .true | some .null => true
    | some .false | none => false) &&
  (if schema.requiresPrimaryKeyNotNull then
    schema.primaryKey.all fun key => key.columns.all fun i => !model.isNull (row.get i)
  else true) &&
  (match schema.organization with
    | .rowid (some i) => (model.asRowId (row.get i)).isSome && model.asRowId (row.get i) == row.rowId?
    | _ => true)

def keyConflict (key : Key schema.Index) (first second : TableRow model schema) : Bool :=
  key.columns.all fun i =>
    !model.isNull (first.get i) && !model.isNull (second.get i) &&
      sem.keyEqual (schema.kind i) (schema.column i).collation (first.get i) (second.get i)

def distinctRows (first second : TableRow model schema) : Bool :=
  (first.rowId?.isNone || first.rowId? != second.rowId?) &&
  (schema.primaryKey.all fun key => !(schema.keyConflict model sem key first second)) &&
  (schema.uniqueKeys.all fun key => !(schema.keyConflict model sem key first second))

def TableValid (rows : List (TableRow model schema)) : Prop :=
  (∀ row ∈ rows, schema.GenerationValid model sem row.cell ∧ schema.rowChecks model sem row = true) ∧
    rows.Pairwise (fun first second => schema.distinctRows model sem first second = true)

instance [DecidableEq Value] (cells : schema.Cells model) :
    Decidable (schema.GenerationValid model sem cells) :=
  inferInstanceAs (Decidable (∀ i, schema.fill model sem (fun j => cells j.val) i = some (cells i)))

instance [DecidableEq Value] (rows : List (TableRow model schema)) :
    Decidable (schema.TableValid model sem rows) :=
  inferInstanceAs (Decidable
    ((∀ row ∈ rows, schema.GenerationValid model sem row.cell ∧ schema.rowChecks model sem row = true) ∧
      rows.Pairwise (fun first second => schema.distinctRows model sem first second = true)))

end TableSchema

abbrev CheckedTable (model : ValueModel Value Affinity) (sem : TableSemantics Value Affinity Expr)
    (schema : TableSchema Affinity Expr) :=
  Constrained (Silmaril.Relational.Table schema.rowKind (schema.RowCell model))
    (schema.TableValid model sem)

abbrev CheckedColumns (model : ValueModel Value Affinity) (sem : TableSemantics Value Affinity Expr)
    (schema : TableSchema Affinity Expr) :=
  Constrained (AlignedColumns schema.rowKind (schema.RowCell model))
    (fun columns => schema.TableValid model sem columns.toRows)

namespace CheckedTable

variable {model : ValueModel Value Affinity} {sem : TableSemantics Value Affinity Expr}
variable {schema : TableSchema Affinity Expr}

def empty : CheckedTable model sem schema :=
  ⟨[], by simp [TableSchema.TableValid]⟩

def rows (table : CheckedTable model sem schema) : List (TableRow model schema) := table.val

def column (table : CheckedTable model sem schema) (i : schema.Index) :
    List ((schema.kind i).Cell model) :=
  table.rows.map fun row => row.cell i

def columnValues (table : CheckedTable model sem schema) (i : schema.Index) : List Value :=
  table.rows.map fun row => row.get i

def eraseRows (rows : List (TableRow model schema)) : List (List Value) :=
  rows.map fun row => List.ofFn row.get

def values (table : CheckedTable model sem schema) : List (List Value) :=
  eraseRows table.rows

def check (rows : List (TableRow model schema)) [Decidable (schema.TableValid model sem rows)] :
    Option (CheckedTable model sem schema) :=
  if h : schema.TableValid model sem rows then some ⟨rows, h⟩ else none

end CheckedTable

namespace CheckedColumns

variable {model : ValueModel Value Affinity} {sem : TableSemantics Value Affinity Expr}
variable {schema : TableSchema Affinity Expr}

def check (columns : AlignedColumns schema.rowKind (schema.RowCell model))
    [Decidable (schema.TableValid model sem columns.toRows)] :
    Option (CheckedColumns model sem schema) :=
  if h : schema.TableValid model sem columns.toRows then some ⟨columns, h⟩ else none

end CheckedColumns

end Silmaril.SQLite.Relational
