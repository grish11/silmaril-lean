module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs

/-! # Connect bounded cleanup to the existing scalar runners -/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry

open Functions.ExceptionalTry (Outcome Plan)
open Core.Module.Functions (Session)
open Core.Closure.Executor (CodeTable)

def ordinarySuite {scope : Source.Scope} (table : CodeTable) (session : Session)
    (actions : List (ModuleEntry.Action scope)) : Outcome Session Completion :=
  match (runPrefix table (actions.length + 1) (.ready session (actions.map .scalar))).2 with
  | .finished reached .normal => ⟨reached, .ok ()⟩
  | .finished reached failure => ⟨reached, .error failure⟩
  | .ready reached _ => ⟨reached, .error .scalarProfile⟩
  | .calling _ _ => ⟨session, .error .scalarProfile⟩

def Completion.isPythonError : Completion → Bool
  | .raised _ | .assertionError => true
  | _ => false

def ordinary {scope : Source.Scope} (table : CodeTable) (session : Session)
    (plan : Plan (ModuleEntry.Action scope)) : Outcome Session Completion :=
  Functions.ExceptionalTry.run (ordinarySuite table) Completion.isPythonError session plan

/-- Preserve the observation delivered before the compound statement,
including its ordered receipts. -/
def seededSuite {scope : Source.Scope} (context : Seeded.CallContext) (incoming : Seeded.Observation)
    (actions : List (ModuleEntry.Action scope)) : Outcome Seeded.Observation Seeded.ModuleFailure :=
  let result := Seeded.runInstructionsIn incoming.residual { context with heap := incoming.heap }
    (actions.map .scalar) incoming.lists
  ⟨{ result with calls := incoming.calls ++ result.calls }, result.completion⟩

def ModuleFailure.isPythonError : Seeded.ModuleFailure → Bool
  | .raised _ => true
  | _ => false

def seeded {scope : Source.Scope} (context : Seeded.CallContext) (incoming : Seeded.Observation)
    (plan : Plan (ModuleEntry.Action scope)) : Seeded.Observation :=
  match incoming.completion with
  | .error _ => incoming
  | .ok () =>
    let result := Functions.ExceptionalTry.run (seededSuite context) ModuleFailure.isPythonError incoming plan
    { result.reached with completion := result.completion }


end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry
