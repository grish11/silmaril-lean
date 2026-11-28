module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NormalTry.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms
public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms

import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.NormalTry

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NormalTry

open Core.Module (ListHeap)
open Core.Module.Functions (Session)
open Core.Module.SeededCall (Namespace)
open Core.Closure.Executor (CodeTable)

theorem ordinary_writes {scope : Source.Scope} (table : CodeTable) (session : Session) (fuel : Nat)
    (writes : List (Write scope)) (rest : List (Run.Instruction scope)) :
    Run.runPrefix table (fuel + writes.length)
      (.ready session (writes.map (fun write => .scalar write.action) ++ rest)) =
      Run.runPrefix table fuel (.ready (writes.foldl
        (fun state write => state.bindGlobal write.name (Run.embed write.value)) session) rest) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.NormalTry.ordinary_writes table session fuel writes rest

theorem seeded_writes {scope : Source.Scope} (space : Namespace) (context : Run.Seeded.CallContext)
    (writes : List (Write scope)) (rest : List (Run.Instruction scope)) (lists : ListHeap) :
    Run.Seeded.runInstructionsIn space context (writes.map (fun write => .scalar write.action) ++ rest) lists =
      Run.Seeded.runInstructionsIn (writes.foldl (fun state write =>
        state.bindGlobal write.name (Run.Seeded.seededValue (Run.embed write.value))) space) context rest lists :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.NormalTry.seeded_writes space context writes rest lists

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NormalTry
