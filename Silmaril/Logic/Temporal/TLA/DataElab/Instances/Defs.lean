module

public import Silmaril.Logic.Temporal.TLA.DataElab.Collections.Defs
public import Silmaril.Logic.Temporal.TLA.Resolution.Instances.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Collections.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Endpoints.Defs

/-! State and action lowering from a paired instance resolution and level check. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Instances

open Resolution Resolution.Instances

private def select (selection : Endpoints.Selection) (checked : CheckedInstances)
    (signature : ExternalSignature) (fragment : Fragment) (maxDepth : Nat) (id : BindingId) :
    Except Endpoints.Diagnostic (CheckedExpr signature fragment) := do
  let (home, body) ← (definitionBody checked.registry id).mapError .lowering
  let site := home.child .body
  let some summary := checked.levels.operatorAt id | throw (.missingLevel site id)
  unless summary.parameters.isEmpty && summary.result.dependencies.isEmpty &&
      summary.requirements.isEmpty do
    throw (.openDefinition site id)
  let level := summary.result.floor
  let accepted : Bool := match selection with
    | .state => level.atMost .state
    | .action => level = .action
  unless accepted do throw (.wrongLevel site selection level)
  (lowerBody checked.registry signature fragment true maxDepth home body (allowInstances := true))
    |>.mapError .lowering

private def lowerStateIn (checked : CheckedInstances) (signature : ExternalSignature)
    (fragment : Fragment) (maxDepth : Nat) (id : BindingId) :
    Except Endpoints.Diagnostic (CheckedExpr signature fragment) := do
  let expression ← select .state checked signature fragment maxDepth id
  if let some site := expression.term.firstPrime then throw (.primeInState site)
  return expression

/-- Lower a closed constant- or state-level source definition with checked
INSTANCE replay. The result has no retained target read. -/
public def lowerState (checked : CheckedInstances) (signature : ExternalSignature)
    (maxDepth : Nat) (id : BindingId) : Except Endpoints.Diagnostic (CheckedExpr signature) :=
  lowerStateIn checked signature .core maxDepth id

/-- Lower a closed action-level source definition with checked INSTANCE replay.
Use the existing endpoint evaluator for the resulting term. -/
public def lowerAction (checked : CheckedInstances) (signature : ExternalSignature)
    (maxDepth : Nat) (id : BindingId) :
    Except Endpoints.Diagnostic (Endpoints.CheckedAction signature) := do
  let expression ← select .action checked signature .core maxDepth id
  return ⟨expression.term, expression.wellFormed⟩

/-- Lower a closed constant- or state-level collection expression through the
paired INSTANCE registry and level certificate. -/
public def lowerCollectionState (checked : CheckedInstances) (signature : ExternalSignature)
    (maxDepth : Nat) (id : BindingId) : Except Endpoints.Diagnostic (CheckedExpr signature .collections) :=
  lowerStateIn checked signature .collections maxDepth id

/-- Lower a closed action-level collection expression with checked INSTANCE
replay. Evaluate it with `Collections.CheckedAction.eval` at two endpoints. -/
public def lowerCollectionAction (checked : CheckedInstances) (signature : ExternalSignature)
    (maxDepth : Nat) (id : BindingId) : Except Endpoints.Diagnostic (Collections.CheckedAction signature) := do
  return ⟨← select .action checked signature .collections maxDepth id⟩

end Silmaril.Logic.Temporal.TLA.DataElab.Instances
