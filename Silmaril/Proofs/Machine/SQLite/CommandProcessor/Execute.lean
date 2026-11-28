module

public import Silmaril.Machine.SQLite.CommandProcessor.Execute.Defs
import Silmaril.Machine.SQLite.CommandProcessor.Thms
import Silmaril.Machine.SQLite.CodeGenerator.Bytecode.Thms
import Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.CommandProcessor

open Silmaril.Machine.SQLite
open Silmaril.Machine.SQLite.CommandProcessor
open Silmaril.SQLite.Relational
open CatalogExecutor (Target profile)

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}
variable {db : State sem} {vm : VirtualMachine.Database} {locate : Target sem → CodeGenerator.Address}
variable {text : String} {stmt : Parser.Statement} {binding : Option (Int32 × Int64)}

theorem execute_eq (parsed : Parser.Represents text stmt)
    (compatible : CodeGenerator.Compatible db vm locate (request db stmt binding)) :
    execute db vm locate text binding = .ok (CatalogExecutor.execute sem db (invocation stmt binding)) := by
  have hp := (parse_iff _ _).2 parsed
  have h := CodeGenerator.executeRequest_eq compatible
  change execute db vm locate text binding =
    .ok ((CatalogExecutor.executor sem).check db (request db stmt binding))
  simp [execute, hp, h, Except.mapError, bind, Except.bind]

theorem execute_iff (parsed : Parser.Represents text stmt)
    (compatible : CodeGenerator.Compatible db vm locate (request db stmt binding))
    (out : CheckedOutcome (profile sem)) :
    execute db vm locate text binding = .ok out ↔
      CatalogExecutor.denote sem db (invocation stmt binding) out := by
  rw [execute_eq parsed compatible, ← CatalogExecutor.execute_eq]
  exact ⟨Except.ok.inj, congrArg Except.ok⟩

end Silmaril.Proofs.Machine.SQLite.CommandProcessor
