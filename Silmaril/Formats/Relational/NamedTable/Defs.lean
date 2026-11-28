module

public import Silmaril.Semantics.Relational.Scan.Database.Defs
public import Silmaril.Formats.Parquet.Reader.Defs
public import Mathlib.Data.List.SplitLengths

/-!
# Named nullable tables at the typed format boundary

Table names are exact database keys under the caller's decidable equality.
Import inserts only at a vacant name and checks the ordered column identities
and kinds against the expected schema. Rows retain their order and multiplicity.
Column identities may repeat because the schema identifies positions separately.
-/

@[expose] public section

namespace Silmaril.Formats.Relational.NamedTable

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet

/-- The existing packed database specialized to ordered typed nullable tables. -/
abbrev Packed (Name Id : Type*) {Kind : Type*} (Value : Kind → Type*) :=
  Database.Packed Name (fun schema : Scan.Schema Id Kind => Scan.Table schema Value)

abbrev Dependent (Name Id : Type*) {Kind : Type*} (Value : Kind → Type*) :=
  Database.Dependent Name (fun schema : Scan.Schema Id Kind => Scan.Table schema Value)

inductive ImportError (Error : Type*) where
  | nameConflict
  | schemaMismatch
  | openError (error : Error)
  | closed
  | readError (error : Error)
  | closeError (error : Error)
  deriving DecidableEq

inductive ExportError where
  | missingName
  | rowCountMismatch (requested available : Nat)
  deriving DecidableEq

variable {Name Id Kind Error Group : Type*} {Value : Kind → Type*}

/-- Equality of the finite ordered schema labels, including width. -/
def schemaMatches [DecidableEq Id] [DecidableEq Kind] (expected actual : Scan.Schema Id Kind) : Bool :=
  decide (List.ofFn expected.kind = List.ofFn actual.kind)

/-- Check name occupancy, the stream outcome, then the schema. Only EOS can
return an updated database. A failure returns the reason without any update. -/
def importCollected [DecidableEq Name] [DecidableEq Id] [DecidableEq Kind]
    (db : Packed Name Id Value) (name : Name) (expected : Scan.Schema Id Kind)
    (collected : Except Error (Events.Observation Id Value Error)) :
    Except (ImportError Error) (Packed Name Id Value) :=
  if (db name).isSome then .error .nameConflict
  else
    match collected with
    | .error error => .error (.openError error)
    | .ok ⟨_, .closed⟩ => .error .closed
    | .ok ⟨_, .readError error⟩ => .error (.readError error)
    | .ok ⟨_, .closeError error⟩ => .error (.closeError error)
    | .ok ⟨table, .eos⟩ =>
      if schemaMatches expected table.schema then
        .ok (Function.update db name (some ⟨table.schema, table.rows⟩))
      else .error .schemaMismatch

def importArrow [DecidableEq Name] [DecidableEq Id] [DecidableEq Kind]
    (db : Packed Name Id Value) (name : Name) (expected : Scan.Schema Id Kind)
    (stream : Events.EventStream Id Value Error) : Except (ImportError Error) (Packed Name Id Value) :=
  importCollected db name expected stream.collect

def importParquet [DecidableEq Name] [DecidableEq Id] [DecidableEq Kind]
    (db : Packed Name Id Value) (name : Name) (expected : Scan.Schema Id Kind)
    (opened : Reader.OpenResult Group Id Value Error) : Except (ImportError Error) (Packed Name Id Value) :=
  importArrow db name expected (Reader.readAll opened)

def importArrowDependent [DecidableEq Name] [DecidableEq Id] [DecidableEq Kind]
    (db : Dependent Name Id Value) (name : Name) (expected : Scan.Schema Id Kind)
    (stream : Events.EventStream Id Value Error) : Except (ImportError Error) (Dependent Name Id Value) :=
  (importArrow db.pack name expected stream).map Database.Packed.unpack

/-- Export from the existing named-table observation. Each length in `sizes`
requests one group, including zeros. Their sum must equal the observed row count. -/
def exportChunks (db : Packed Name Id Value) (name : Name) (sizes : List Nat) :
    Except ExportError (Σ schema : Scan.Schema Id Kind, List (Scan.Table schema Value)) :=
  match Scan.observePacked db name with
  | none => .error .missingName
  | some table =>
    if sizes.sum = table.rowCount then .ok ⟨table.schema, sizes.splitLengths table.rows⟩
    else .error (.rowCountMismatch sizes.sum table.rowCount)

def exportArrow (db : Packed Name Id Value) (name : Name) (sizes : List Nat) :
    Events.EventStream Id Value ExportError :=
  (exportChunks db name sizes).map fun ⟨schema, chunks⟩ =>
    ⟨schema, ⟨chunks.map AlignedColumns.ofRows, .eos⟩⟩

/-- Produce a typed reader source with one row-list descriptor per requested
group. A later writer can consume the groups at their original schema. -/
def exportParquet (db : Packed Name Id Value) (name : Name) (sizes : List Nat) :
    Except ExportError (Σ schema : Scan.Schema Id Kind,
      Reader.Source (Reader.RowGroup schema Value) schema Value ExportError) :=
  (exportChunks db name sizes).map fun ⟨schema, chunks⟩ => ⟨schema, ⟨chunks, Except.ok, fun _ => .ok ()⟩⟩

def exportArrowDependent (db : Dependent Name Id Value) (name : Name) (sizes : List Nat) :
    Events.EventStream Id Value ExportError :=
  exportArrow db.pack name sizes

end Silmaril.Formats.Relational.NamedTable
