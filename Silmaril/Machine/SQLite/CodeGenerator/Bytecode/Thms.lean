module

public import Silmaril.Machine.SQLite.CodeGenerator.Bytecode.Defs
public import Silmaril.Machine.SQLite.CodeGenerator.Thms
import Silmaril.Proofs.Machine.SQLite.CodeGenerator.Bytecode

public section

namespace Silmaril.Machine.SQLite.CodeGenerator

open Silmaril.SQLite.Relational
open CatalogExecutor (Names Target)

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

/-- For a represented bound point, the compiled VM yields exactly the D3
lookup result. The unbound path requires no VM table. -/
theorem run_compile {vm : VirtualMachine.Database} {address : Address} {stmt : Prepared sem}
    (h : stmt.key.isSome → Represents vm address stmt.plan.target) :
    run vm (compile address stmt) =
      .ok ⟨stmt.plan.label, stmt.key.bind stmt.plan.target.lookup⟩ :=
  Proofs.Machine.SQLite.CodeGenerator.run_compile h

/-- The whole classified D3 reply and connection agree, including scope
rejection, resolution and bind failure, unbound, point hit and point miss. -/
theorem executeRequest_eq {db : State sem} {vm : VirtualMachine.Database}
    {locate : Target sem → Address} {request : CheckedRequest Names}
    (h : Compatible db vm locate request) :
    executeRequest db vm locate request = .ok ((CatalogExecutor.executor sem).check db request) :=
  Proofs.Machine.SQLite.CodeGenerator.executeRequest_eq h

end Silmaril.Machine.SQLite.CodeGenerator
