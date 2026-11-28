module

public import Silmaril.Machine.SQLite.CommandProcessor.Execute.Defs
public import Silmaril.Machine.SQLite.CodeGenerator.Bytecode.Thms
public import Silmaril.Machine.SQLite.CommandProcessor.Thms
import Silmaril.Proofs.Machine.SQLite.CommandProcessor.Execute

public section

namespace Silmaril.Machine.SQLite.CommandProcessor

open Silmaril.SQLite.Relational
open CatalogExecutor (Target profile)

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}
variable {db : State sem} {vm : VirtualMachine.Database} {locate : Target sem → CodeGenerator.Address}
variable {text : String} {stmt : Parser.Statement} {binding : Option (Int32 × Int64)}

theorem execute_eq (parsed : Parser.Represents text stmt)
    (compatible : CodeGenerator.Compatible db vm locate (request db stmt binding)) :
    execute db vm locate text binding = .ok (CatalogExecutor.execute sem db (invocation stmt binding)) :=
  Proofs.Machine.SQLite.CommandProcessor.execute_eq parsed compatible

/-- Successful transport through the compiled pipeline observes exactly the
D3 catalog relation on the parsed invocation, including ordinary D3 errors. -/
theorem execute_iff (parsed : Parser.Represents text stmt)
    (compatible : CodeGenerator.Compatible db vm locate (request db stmt binding))
    (out : CheckedOutcome (profile sem)) :
    execute db vm locate text binding = .ok out ↔
      CatalogExecutor.denote sem db (invocation stmt binding) out :=
  Proofs.Machine.SQLite.CommandProcessor.execute_iff parsed compatible out

end Silmaril.Machine.SQLite.CommandProcessor
