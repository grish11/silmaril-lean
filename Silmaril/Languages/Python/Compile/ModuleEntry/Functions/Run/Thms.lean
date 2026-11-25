module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs
public import Silmaril.Languages.Python.Core.Module.Functions.Thms
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Prefix

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run

theorem seed_lookup (globals : Core.Module.Globals) (heap : Core.Closure.Heap) (name : String) :
    (seed globals heap).globals name = (globals.lookup name).map embed := rfl

theorem invoke_current_globals {scope : Source.Scope} (session : Core.Module.Functions.Session)
    (table : Core.Closure.Executor.CodeTable) (target : Core.Module.Functions.Destination)
    (name : String) (arguments : List Core.Module.Functions.Operand) (remaining : List (Instruction scope)) :
    advance table (.ready session (.call target name arguments :: remaining)) =
      ([], .calling (session.prepareCall target (.readGlobal name) arguments) remaining) := rfl

theorem runPrefix_append {scope : Source.Scope} (table : Core.Closure.Executor.CodeTable)
    (first second : Nat) (initial : State scope) :
    let (log, paused) := runPrefix table first initial
    let (tail, residual) := runPrefix table second paused
    runPrefix table (first + second) initial = (log ++ tail, residual) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.runPrefix_append table first second initial

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run
