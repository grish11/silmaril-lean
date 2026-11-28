module

public import Silmaril.Machine.SQLite.CodeGenerator.Defs

public section

namespace Silmaril.Proofs.Machine.SQLite.CodeGenerator

open Silmaril.Machine.SQLite.CodeGenerator
open Silmaril.SQLite.Relational
open CatalogExecutor (Names profile)

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

theorem prepare_iff (db : State sem) (request : CheckedRequest Names)
    (out : Except PrepareError (Prepared sem)) :
    prepare db request = out ↔ Prepares db request out := by
  constructor
  · rintro rfl
    cases request with
    | unsupported feature => exact .unsupported feature
    | invoke call =>
      cases resolve : CatalogExecutor.resolve db.catalog call.statement with
      | error error =>
        simpa [prepare, Executor.prepare, CatalogExecutor.executor, resolve, Except.mapError] using
          (Prepares.resolveError (db := db) (call := call) resolve)
      | ok plan =>
        simpa [prepare, Executor.prepare, CatalogExecutor.executor, resolve, Except.mapError] using
          (Prepares.resolved (db := db) (call := call) resolve)
  · intro h
    cases h with
    | unsupported => rfl
    | resolveError resolve =>
      change CatalogExecutor.resolve _ _ = _ at resolve
      simp [prepare, Executor.prepare, CatalogExecutor.executor, resolve, Except.mapError]
    | resolved resolve =>
      change CatalogExecutor.resolve _ _ = _ at resolve
      simp [prepare, Executor.prepare, CatalogExecutor.executor, resolve, Except.mapError]

end Silmaril.Proofs.Machine.SQLite.CodeGenerator
