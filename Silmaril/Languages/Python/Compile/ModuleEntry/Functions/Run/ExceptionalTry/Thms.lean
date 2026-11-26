module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry.Thms
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry

open Core.Module (ListHeap)
open Core.Module.Functions (Session)
open Core.Module.SeededCall (Namespace)
open Core.Closure.Executor (CodeTable)

theorem ordinary_scalar_trace {scope : Source.Scope} (table : CodeTable) (session : Session)
    (actions : List (ModuleEntry.Action scope)) :
    ∃ reached completion,
      runPrefix table (actions.length + 1) (.ready session (actions.map .scalar)) =
        ([], .finished reached completion) ∧ reached.heap = session.heap ∧ reached.lists = session.lists :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.ordinary_scalar_trace table session actions

theorem seeded_scalar_carriers {scope : Source.Scope} (space : Namespace) (context : Seeded.CallContext)
    (actions : List (ModuleEntry.Action scope)) (lists : ListHeap) :
    let outcome := Seeded.runInstructionsIn space context (actions.map .scalar) lists
    outcome.heap = context.heap ∧ outcome.lists = lists ∧ outcome.calls = [] ∧
      outcome.residual.builtins = space.builtins :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.seeded_scalar_carriers space context actions lists

theorem seededSuite_carriers {scope : Source.Scope} (context : Seeded.CallContext)
    (incoming : Seeded.Observation) (actions : List (ModuleEntry.Action scope)) :
    let reached := (seededSuite context incoming actions).reached
    reached.heap = incoming.heap ∧ reached.lists = incoming.lists ∧ reached.calls = incoming.calls ∧
      reached.residual.builtins = incoming.residual.builtins := by
  have ⟨heap, lists, calls, builtins⟩ := seeded_scalar_carriers incoming.residual
    { context with heap := incoming.heap } actions incoming.lists
  exact ⟨heap, lists, by simp [seededSuite, calls], builtins⟩

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry
