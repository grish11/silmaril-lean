module

public import Silmaril.Machine.SQLite.TrackA.Read.Adapter.Thms
public import Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Thms

@[expose] public section

namespace Silmaril.SQLite.Relational.Bridge

open Silmaril.Machine.SQLite.TrackA
open Silmaril.Machine.SqliteVfs
open CatalogExecutor (SqlSnapshot Names ResolveError Target)

inductive ReadFailure where
  | trackA (error : Read.ReadError)
  | nanReal (bits : UInt64)
  deriving DecidableEq

/-- A decoded string carries characters, so its D1 representation uses UTF-8.
A REAL retains its bits when those bits are admitted by D1. -/
def transferCell : Formats.Sqlite.Value → Except ReadFailure SqlValue
  | .null => .ok .null
  | .integer n => .ok (.integer n)
  | .blob bytes => .ok (.blob bytes.data)
  | .text text => .ok (.text (Text.utf8 text))
  | .real bits =>
    match Real.ofBits bits with
    | some real => .ok (.real real)
    | none => .error (.nanReal bits)

def transferResult : Read.Result → Except ReadFailure (Option SqlValue)
  | .error error => .error (.trackA error)
  | .ok none => .ok none
  | .ok (some value) => (transferCell value).map some

variable {Expr Backing : Type} {sem : TableSemantics SqlValue Affinity Expr}

abbrev profile (sem : TableSemantics SqlValue Affinity Expr) (Backing : Type) : Profile where
  Value := SqlValue
  Catalog := SqlSnapshot sem
  Ref := Names
  Target := Target sem
  PrepareError := ResolveError
  ReadError := ReadFailure
  Backing := Backing
  Cache := PageRead.Cache
  Exchange := Exchange

abbrev Locate (sem : TableSemantics SqlValue Affinity Expr) := Target sem → Read.Adapter.Acquire

def transfer (observed : Read.Outcome Backing) : ReadOutcome (profile sem Backing) :=
  ⟨transferResult observed.result, observed.file, observed.cache, observed.exchanges⟩

/-- The caller assigns a checked catalog target its physical Pager request.
The executable backend uses Track A's composed VDBE leaf read. -/
def executor (backing : Handler Backing) (locate : Locate sem) : Executor (profile sem Backing) where
  resolve := CatalogExecutor.resolve
  read state query :=
    let request := locate query.1
    transfer (Read.runComposed backing state.1 state.2 request.target request.page query.2)

def execute (backing : Handler Backing) (locate : Locate sem)
    (db : Connection (profile sem Backing)) (call : Invocation Names) :
    CheckedOutcome (profile sem Backing) :=
  (executor backing locate).check db (CatalogExecutor.classify db.catalog call)

/-- Facts about the D input establish which plan and binding drive the read. -/
structure Bound (db : Connection (profile sem Backing)) (call : Invocation Names)
    (plan : Plan (Target sem)) (key : Int64) : Prop where
  admitted : CatalogExecutor.classify db.catalog call = .invoke call
  resolved : CatalogExecutor.resolve db.catalog call.statement = .ok plan
  binding : call.binding = some (1, key)

/-- The statement result and whole post-connection observed across the boundary.
The D plan supplies the label, and the input D connection supplies the catalog,
session and history prefix. -/
structure Corresponds (before : Connection (profile sem Backing)) (plan : Plan (Target sem))
    (observed : Read.Outcome Backing) (out : Outcome (profile sem Backing)) : Prop where
  result : out.1 = match transferResult observed.result with
    | .ok cell => .ok ⟨plan.label, cell⟩
    | .error error => .error (.run error)
  catalog : out.2.catalog = before.catalog
  session : out.2.session = before.session
  backing : out.2.backing = observed.file
  cache : out.2.cache = observed.cache
  exchanges : out.2.exchanges = before.exchanges ++ observed.exchanges

/-- Agreement at a key between the input decoded leaf and the checked catalog.
The catalog projection must be the second field read by Track A's VDBE program.
A miss requires absence in the catalog. This is a condition on the two data models before
observing any execution. -/
def Projected (target : Target sem) (table : Formats.Sqlite.Vdbe.Table) (key : Int64) : Prop :=
  target.column.val = 1 ∧
    match table.get key.toInt with
    | none => target.Matches key none
    | some row => ∃ cell, transferCell (row[1]?.getD .null) = .ok cell ∧
        target.Matches key (some cell)

/-- The same snapshot and owned vacant slot used to admit A's cold leaf read. -/
structure ColdLeaf (db : Connection (profile sem FileState)) (request : Read.Adapter.Acquire)
    (table : Formats.Sqlite.Vdbe.Table) where
  image : Formats.Sqlite.File.Image
  view : Formats.Sqlite.File.View
  pageSize : request.page.size = image.header.pageSize
  snapshot : db.backing.bytes = image.source.toList
  found : image.page? request.page.number = some view
  live : (db.backing.mode request.page.handle).isNone = false
  range : ReadRange request.page.offset request.page.size
  owned : db.cache request.target = some .vacant
  decoded : FileView.VdbeLeaf.table? view
    (FileView.Admission.VdbeLeaf.btreeHeaderOffset request.page.number) = some table

/-- The catalog-only executor observes the same catalog and session. This
projection erases the backing, cache and exchanges. -/
def forgetStorage (db : Connection (profile sem Backing)) : Connection (CatalogExecutor.profile sem) :=
  ⟨db.catalog, (), (), [], db.session⟩

end Silmaril.SQLite.Relational.Bridge
