module

public import Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.CodeGenerator

open Silmaril.SQLite.Relational
open CatalogExecutor (Names ResolveError Target profile)

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

/-- The planner consumes a D3 catalog request. In this profile the planning state
is the D3 connection and a prepared plan has one initially empty bind slot. -/
abbrev State (sem : TableSemantics SqlValue Affinity Expr) := Connection (profile sem)

abbrev Prepared (sem : TableSemantics SqlValue Affinity Expr) :=
  Silmaril.SQLite.Relational.Prepared (Target sem)

inductive PrepareError where
  | unsupported (feature : String)
  | resolve (error : ResolveError)
  deriving DecidableEq, Repr

/-- The single available plan is D3's resolved target and projection label.
A caller supplies the checked request, normally from `CatalogExecutor.classify`. -/
def prepare (db : State sem) (request : CheckedRequest Names) :
    Except PrepareError (Prepared sem) :=
  match request with
  | .unsupported feature => .error (.unsupported feature)
  | .invoke call => ((CatalogExecutor.executor sem).prepare db call.statement).mapError .resolve

/-- Abstract planning outcomes use the D3 resolver judgment. Bindings in the
request are consumed only by binding or execution. -/
inductive Prepares (db : State sem) :
    CheckedRequest Names → Except PrepareError (Prepared sem) → Prop where
  | unsupported (feature : String) :
      Prepares db (.unsupported feature) (.error (.unsupported feature))
  | resolveError {call error}
      (resolves : (CatalogExecutor.reference sem).resolves db.catalog call.statement (.error error)) :
      Prepares db (.invoke call) (.error (.resolve error))
  | resolved {call plan}
      (resolves : (CatalogExecutor.reference sem).resolves db.catalog call.statement (.ok plan)) :
      Prepares db (.invoke call) (.ok ⟨plan, none⟩)

end Silmaril.Machine.SQLite.CodeGenerator
