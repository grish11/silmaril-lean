module

public import Silmaril.Semantics.SQLite.Relational.Statement.Defs
public import Silmaril.Semantics.Relational.Query.Defs

@[expose] public section

namespace Silmaril.SQLite.Relational

open Silmaril.Relational (QueryRel StatefulQueryRel)

/-- The types supplied by the value, catalog and backing layers. -/
structure Profile where
  Value : Type
  Catalog : Type
  Ref : Type
  Target : Type
  PrepareError : Type
  ReadError : Type
  Backing : Type
  Cache : Type
  Exchange : Type

/-- Session observations preserved by the read-only fragment. -/
structure Session where
  autocommit : Bool := true
  changes : Int64 := 0
  totalChanges : Int64 := 0
  lastInsertRowid : Int64 := 0
  deriving DecidableEq, Repr

/-- The connection carried through every successful or defined failing call. -/
structure Connection (p : Profile) where
  catalog : p.Catalog
  backing : p.Backing
  cache : p.Cache
  exchanges : List p.Exchange := []
  session : Session := {}

/-- One backend read. Exchanges are the suffix from this call alone. The
backend's poststate is observable even on failure. -/
structure ReadOutcome (p : Profile) where
  result : Except p.ReadError (Option p.Value)
  backing : p.Backing
  cache : p.Cache
  exchanges : List p.Exchange

abbrev Result (p : Profile) :=
  Except (StatementError p.PrepareError p.ReadError) (SelectResult p.Value)

abbrev Outcome (p : Profile) := Result p × Connection p

/-- The resolver supplies the label and target. The reader performs a lookup
using the actual input backing and cache. -/
structure Executor (p : Profile) where
  resolve : p.Catalog → Statement p.Ref → Except p.PrepareError (Plan p.Target)
  read : p.Backing × p.Cache → p.Target × Int64 → ReadOutcome p

variable {p : Profile}

def Executor.prepare (exec : Executor p) (db : Connection p) (stmt : Statement p.Ref) :
    Except p.PrepareError (Prepared p.Target) :=
  match exec.resolve db.catalog stmt with
  | .ok plan => .ok ⟨plan, none⟩
  | .error error => .error error

/-- Publish the read observation and append completed exchanges, including on
the error path. -/
def ReadOutcome.finish (read : ReadOutcome p) (db : Connection p) (label : String) : Outcome p :=
  let result := match read.result with
    | .ok cell => .ok ⟨label, cell⟩
    | .error error => .error (.run error)
  let after := { db with
    backing := read.backing
    cache := read.cache
    exchanges := db.exchanges ++ read.exchanges }
  (result, after)

/-- Materialize one fresh run of a plan in the session it was resolved for. -/
def Executor.run (exec : Executor p) (db : Connection p) (stmt : Prepared p.Target) : Outcome p :=
  match stmt.key with
  | none => (.ok ⟨stmt.plan.label, none⟩, db)
  | some key => (exec.read (db.backing, db.cache) (stmt.plan.target, key)).finish db stmt.plan.label

/-- Preparation precedes binding. Defined errors at either stage stop before
the backend is called. -/
def Executor.execute (exec : Executor p) (db : Connection p) (call : Invocation p.Ref) : Outcome p :=
  match exec.prepare db call.statement with
  | .error error => (.error (.prepare error), db)
  | .ok stmt =>
    match call.binding with
    | none => exec.run db stmt
    | some (index, key) =>
      match stmt.bindInt64 index key with
      | (.error error, _) => (.error (.bind error), db)
      | (.ok (), bound) => exec.run db bound

/-- Independent resolver and lookup judgments, including errors and complete
backend poststate. -/
structure Reference (p : Profile) where
  resolves : QueryRel p.Catalog (Statement p.Ref) (Except p.PrepareError (Plan p.Target))
  reads : QueryRel (p.Backing × p.Cache) (p.Target × Int64) (ReadOutcome p)

inductive Reference.Executes (ref : Reference p) :
    StatefulQueryRel (Connection p) (Invocation p.Ref) (Result p) where
  | prepareError {db call error}
      (resolve : ref.resolves db.catalog call.statement (.error error)) :
      Executes ref db call (.error (.prepare error)) db
  | bindError {db call plan index key}
      (resolve : ref.resolves db.catalog call.statement (.ok plan))
      (binding : call.binding = some (index, key)) (range : index ≠ 1) :
      Executes ref db call (.error (.bind .range)) db
  | unbound {db call plan}
      (resolve : ref.resolves db.catalog call.statement (.ok plan))
      (binding : call.binding = none) :
      Executes ref db call (.ok ⟨plan.label, none⟩) db
  | seek {db call plan key read}
      (resolve : ref.resolves db.catalog call.statement (.ok plan))
      (binding : call.binding = some (1, key))
      (lookup : ref.reads (db.backing, db.cache) (plan.target, key) read) :
      Executes ref db call (read.finish db plan.label).1 (read.finish db plan.label).2

/-- Soundness of each executable dependency on its public observation. -/
structure Executor.Sound (exec : Executor p) (ref : Reference p) : Prop where
  resolve : (QueryRel.ofTotal exec.resolve).Sound ref.resolves
  read : (QueryRel.ofTotal exec.read).Sound ref.reads

/-- Completeness uses the same result equality, including backing and cache. -/
structure Executor.Complete (exec : Executor p) (ref : Reference p) : Prop where
  resolve : (QueryRel.ofTotal exec.resolve).Complete ref.resolves
  read : (QueryRel.ofTotal exec.read).Complete ref.reads

def Executor.denote (exec : Executor p) : QueryRel (Connection p) (Invocation p.Ref) (Outcome p) :=
  QueryRel.ofTotal exec.execute

def Reference.denote (ref : Reference p) : QueryRel (Connection p) (Invocation p.Ref) (Outcome p) :=
  ref.Executes.toQueryRel

/-- Successful results and their poststates in call order, plus the first defined error. -/
structure BatchResult (p : Profile) where
  completed : List (SelectResult p.Value × Connection p)
  failure : Option (StatementError p.PrepareError p.ReadError)

abbrev BatchOutcome (p : Profile) := BatchResult p × Connection p

def BatchOutcome.prepend (completed : SelectResult p.Value × Connection p) (outcome : BatchOutcome p) :
    BatchOutcome p :=
  (⟨completed :: outcome.1.completed, outcome.1.failure⟩, outcome.2)

/-- Continue from the first batch's actual poststate only on success. -/
def BatchOutcome.andThen (first : BatchOutcome p) (next : Connection p → BatchOutcome p) :
    BatchOutcome p :=
  match first.1.failure with
  | some _ => first
  | none =>
    let rest := next first.2
    (⟨first.1.completed ++ rest.1.completed, rest.1.failure⟩, rest.2)

/-- Execute a sequence of fresh invocations on a single connection. -/
def Executor.executeBatch (exec : Executor p) (db : Connection p) :
    List (Invocation p.Ref) → BatchOutcome p
  | [] => (⟨[], none⟩, db)
  | call :: rest =>
    match exec.execute db call with
    | (.error error, after) => (⟨[], some error⟩, after)
    | (.ok result, after) => (exec.executeBatch after rest).prepend (result, after)

inductive Reference.BatchExecutes (ref : Reference p) :
    Connection p → List (Invocation p.Ref) → BatchOutcome p → Prop where
  | nil (db : Connection p) : BatchExecutes ref db [] (⟨[], none⟩, db)
  | stop {db call rest error after} (head : ref.Executes db call (.error error) after) :
      BatchExecutes ref db (call :: rest) (⟨[], some error⟩, after)
  | next {db call rest result after out}
      (head : ref.Executes db call (.ok result) after) (tail : BatchExecutes ref after rest out) :
      BatchExecutes ref db (call :: rest) (out.prepend (result, after))

end Silmaril.SQLite.Relational
