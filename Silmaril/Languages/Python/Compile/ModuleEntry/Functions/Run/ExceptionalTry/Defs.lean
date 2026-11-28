module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs

/-! # Connect bounded cleanup to the existing scalar runners -/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry

open Functions.ExceptionalTry (HandlerOperations Outcome Plan)
open Core.Module.Functions (Session)
open Core.Closure.Executor (CodeTable)

def ordinarySuite {scope : Source.Scope} (table : CodeTable) (session : Session)
    (actions : List (ModuleEntry.Action scope)) : Outcome Session Completion :=
  match (runPrefix table (actions.length + 1) (.ready session (actions.map .scalar))).2 with
  | .finished reached .normal => ⟨reached, .ok ()⟩
  | .finished reached failure => ⟨reached, .error failure⟩
  | .ready reached _ => ⟨reached, .error .scalarProfile⟩
  | .calling _ _ => ⟨session, .error .scalarProfile⟩

def ordinary {scope : Source.Scope} (table : CodeTable) (session : Session)
    (plan : Plan (ModuleEntry.Action scope)) : Outcome Session Completion :=
  Functions.ExceptionalTry.run (ordinarySuite table) Completion.isPythonError handlerOperations session plan

/-- Preserve the observation delivered before the compound statement,
including its ordered receipts. -/
def seededSuite {scope : Source.Scope} (context : Seeded.CallContext) (incoming : Seeded.Observation)
    (actions : List (ModuleEntry.Action scope)) : Outcome Seeded.Observation Seeded.ModuleFailure :=
  let result := Seeded.runInstructionsIn incoming.residual { context with heap := incoming.heap }
    (actions.map .scalar) incoming.lists
  ⟨{ result with calls := incoming.calls ++ result.calls }, result.completion⟩

def seeded {scope : Source.Scope} (context : Seeded.CallContext) (incoming : Seeded.Observation)
    (plan : Plan (ModuleEntry.Action scope)) : Seeded.Observation :=
  match incoming.completion with
  | .error _ => incoming
  | .ok () =>
    let operations : HandlerOperations Seeded.Observation Seeded.ModuleFailure :=
      { testClass := fun observed => Seeded.matchHandler observed.residual
        bindCaught := fun observed name pending =>
          (Seeded.bindCaught observed.residual name pending).map fun residual => { observed with residual }
        unbind := fun observed name => { observed with residual := observed.residual.unbindGlobal name } }
    let result := Functions.ExceptionalTry.run (seededSuite context) Seeded.ModuleFailure.isPythonError
      operations incoming plan
    { result.reached with completion := result.completion }


end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry
