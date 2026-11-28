module

public import Silmaril.Machine.SQLite.CodeGenerator.Defs
import Silmaril.Proofs.Machine.SQLite.CodeGenerator.Prepare

public section

namespace Silmaril.Machine.SQLite.CodeGenerator

open Silmaril.SQLite.Relational
open CatalogExecutor (Names)

theorem prepare_iff {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}
    (db : State sem) (request : CheckedRequest Names) (out : Except PrepareError (Prepared sem)) :
    prepare db request = out ↔ Prepares db request out :=
  Proofs.Machine.SQLite.CodeGenerator.prepare_iff db request out

end Silmaril.Machine.SQLite.CodeGenerator
