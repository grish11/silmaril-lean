module

public import Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Defs
public import Silmaril.Semantics.SQLite.Relational.Fragment.Thms
import Silmaril.Proofs.Semantics.SQLite.Relational.Executor.CatalogCorrectness

public section

namespace Silmaril.SQLite.Relational.CatalogExecutor

open Silmaril.Relational (QueryRel)

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

/-- The checked table's rowid uniqueness makes lookup exact for row membership. -/
theorem Target.lookup_iff (target : Target sem) (key : Int64) (cell : Option SqlValue) :
    target.lookup key = cell ↔ target.Matches key cell :=
  Proofs.Semantics.SQLite.Relational.Executor.Catalog.lookup_iff target key cell

theorem executor_sound (sem : TableSemantics SqlValue Affinity Expr) :
    (executor sem).Sound (reference sem) :=
  Proofs.Semantics.SQLite.Relational.Executor.Catalog.executor_sound sem

theorem executor_complete (sem : TableSemantics SqlValue Affinity Expr) :
    (executor sem).Complete (reference sem) :=
  Proofs.Semantics.SQLite.Relational.Executor.Catalog.executor_complete sem

/-- Equality includes scope rejection and the final connection on every branch. -/
theorem execute_eq (sem : TableSemantics SqlValue Affinity Expr) :
    QueryRel.ofTotal (execute sem) = denote sem :=
  Proofs.Semantics.SQLite.Relational.Executor.Catalog.execute_eq sem

end Silmaril.SQLite.Relational.CatalogExecutor
