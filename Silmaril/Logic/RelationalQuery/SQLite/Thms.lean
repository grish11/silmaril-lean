module

public import Silmaril.Logic.RelationalQuery.SQLite.Defs
public import Silmaril.Logic.RelationalQuery.Thms
import Silmaril.Proofs.Logic.RelationalQuery.SQLite.Laws

public section

namespace Silmaril.SQLite.Relational.CatalogExecutor.PointRead

open Silmaril.Relational

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr} {snapshot : SqlSnapshot sem}

/-- The checked interpreter returns the labeled point result for every admitted read. -/
theorem execute_pointRead (db : Connection (profile sem)) (read : PointRead db.catalog)
    (key : Int64) : (execute sem db (read.invocation key)).1 = .statement (.ok (read.result key)) :=
  Proofs.execute_pointRead db read key

/-- The reference judgment has exactly the same successful result, observing only the reply. -/
theorem denote_pointRead (db : Connection (profile sem)) (read : PointRead db.catalog)
    (key : Int64) (observed : SelectResult SqlValue) :
    (∃ after, denote sem db (read.invocation key) (.statement (.ok observed), after)) ↔
      observed = read.result key :=
  Proofs.denote_pointRead db read key observed

/-- Institution evaluation applies the caller's test to a present projected cell. -/
theorem eval_sentence (read : PointRead snapshot) (key : Int64) (test : SqlValue → Bool) :
    DatabaseQuery.eval (queryModel snapshot) (read.sentence key test) = (read.result key).cell.any test :=
  Proofs.eval_sentence read key test

/-- A successful projection of NULL contributes a row, just like any other value. -/
theorem eval_exists (read : PointRead snapshot) (key : Int64) :
    DatabaseQuery.eval (queryModel snapshot) (read.sentence key (fun _ => true)) =
      (read.result key).cell.isSome :=
  (read.eval_sentence key _).trans Option.any_true

/-- Satisfaction is equivalent to an admitted reference reply with a cell passing the test. -/
theorem sat_iff_denote (db : Connection (profile sem)) (read : PointRead db.catalog)
    (key : Int64) (test : SqlValue → Bool) :
    DatabaseQuery.eval (queryModel db.catalog) (read.sentence key test) = true ↔
      ∃ result after, denote sem db (read.invocation key) (.statement (.ok result), after) ∧
        result.cell.any test = true :=
  Proofs.sat_iff_denote db read key test

end Silmaril.SQLite.Relational.CatalogExecutor.PointRead

namespace Silmaril.SQLite.Relational.CatalogExecutor.CatalogPointRead

open Silmaril.Relational

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr} {catalog : TableCatalog Affinity Expr}

/-- A declared point projection passes the checked executor's scope guard in any compatible snapshot. -/
theorem classify_invocation (read : CatalogPointRead catalog) (snapshot : SqlSnapshot sem)
    (compatible : snapshot.catalog.tables = catalog) (key : Int64) :
    classify snapshot (read.invocation key) = .invoke (read.invocation key) :=
  Proofs.classify_invocation read snapshot compatible key

/-- The checked resolver selects the projected column and the compatible snapshot's table. -/
theorem resolve_invocation (read : CatalogPointRead catalog) (snapshot : SqlSnapshot sem)
    (compatible : snapshot.catalog.tables = catalog) (key : Int64) :
    resolve snapshot (read.invocation key).statement =
      .ok ⟨read.target snapshot compatible, read.schema.name read.column⟩ :=
  Proofs.resolve_invocation read snapshot compatible key

/-- The checked interpreter returns the projection label and optional cell. -/
theorem execute_pointRead (read : CatalogPointRead catalog) (db : Connection (profile sem))
    (compatible : db.catalog.catalog.tables = catalog) (key : Int64) :
    (execute sem db (read.invocation key)).1 = .statement (.ok (read.result db.catalog compatible key)) :=
  Proofs.execute_pointRead read db compatible key

/-- Evaluation in a compatible snapshot tests the optional cell returned there. -/
theorem eval_sentence (read : CatalogPointRead catalog) (snapshot : SqlSnapshot sem)
    (compatible : snapshot.catalog.tables = catalog) (key : Int64) (test : SqlValue → Bool) :
    DatabaseQuery.eval (queryModelOfSnapshot snapshot compatible) (read.sentence key test) =
      (read.result snapshot compatible key).cell.any test :=
  Proofs.eval_sentence read snapshot compatible key test

/-- Satisfaction is equivalent to a successful reference reply with a present cell passing the test. -/
theorem sat_iff_denote (read : CatalogPointRead catalog) (db : Connection (profile sem))
    (compatible : db.catalog.catalog.tables = catalog) (key : Int64) (test : SqlValue → Bool) :
    DatabaseQuery.eval (queryModelOfSnapshot db.catalog compatible) (read.sentence key test) = true ↔
      ∃ result after, denote sem db (read.invocation key) (.statement (.ok result), after) ∧
        result.cell.any test = true :=
  Proofs.sat_iff_denote read db compatible key test

end Silmaril.SQLite.Relational.CatalogExecutor.CatalogPointRead
