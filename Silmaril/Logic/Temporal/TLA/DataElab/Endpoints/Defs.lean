module

public import Silmaril.Logic.Temporal.TLA.DataElab.Defs
public import Silmaril.Logic.Temporal.TLA.Resolution.Levels.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs

/-! Level-checked selection and source/target evaluation for data expressions. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Endpoints

open Resolution

universe u

public section

inductive Selection where
  | state | action
  deriving DecidableEq, Repr

inductive Diagnostic where
  | levels (diagnostic : Levels.Diagnostic)
  | lowering (diagnostic : DataElab.Diagnostic)
  | missingLevel (site : Site) (id : BindingId)
  | openDefinition (site : Site) (id : BindingId)
  | wrongLevel (site : Site) (expected : Selection) (actual : Levels.Level)
  | primeInState (site : Site)
  deriving DecidableEq, Repr

/-- A single rigid assignment and both flexible endpoint assignments. -/
structure EndpointValuation (V : Type u) where
  rigid : BindingId → V
  source : BindingId → V
  target : BindingId → V

/-- A closed, supported action-level expansion from the checked registry. -/
structure CheckedAction (signature : ExternalSignature) where
  private mk ::
  term : Term signature
  wellFormed : term.isWellFormed [] = true

@[expose] noncomputable def CheckedAction.eval {V : Type u} {signature : ExternalSignature}
    (action : CheckedAction signature) (ops : DataOperations V) (B : Booleans V)
    (external : ExternalInterpretation V signature) (endpoints : EndpointValuation V) : V :=
  action.term.eval ops B external ⟨endpoints.rigid, endpoints.source⟩
    (fun _ => ops.enum []) endpoints.target

end

private def select (selection : Selection) (registry : CheckedRegistry)
    (externalLevels : Levels.ExternalLevels) (signature : ExternalSignature)
    (maxDepth : Nat) (id : BindingId) : Except Diagnostic (CheckedExpr signature) := do
  let (home, body) ← (definitionBody registry id).mapError .lowering
  let checked ← (Levels.check registry externalLevels).mapError .levels
  let site := home.child .body
  let some summary := checked.operatorAt id | throw (.missingLevel site id)
  unless summary.parameters.isEmpty && summary.result.dependencies.isEmpty &&
      summary.requirements.isEmpty do
    throw (.openDefinition site id)
  let level := summary.result.floor
  let accepted : Bool := match selection with
    | .state => level.atMost .state
    | .action => level = .action
  unless accepted do throw (.wrongLevel site selection level)
  (lowerBody registry signature true maxDepth home body).mapError .lowering

/-- Check the exact registry and select a closed constant- or state-level
definition. Its expanded value must be independent of a target endpoint. -/
public def lowerState (registry : CheckedRegistry) (externalLevels : Levels.ExternalLevels)
    (signature : ExternalSignature) (maxDepth : Nat) (id : BindingId) :
    Except Diagnostic (CheckedExpr signature) := do
  let expression ← select .state registry externalLevels signature maxDepth id
  if let some site := expression.term.firstPrime then throw (.primeInState site)
  return expression

/-- Check the exact registry and select a closed action-level definition in
the supported data fragment. -/
public def lowerAction (registry : CheckedRegistry) (externalLevels : Levels.ExternalLevels)
    (signature : ExternalSignature) (maxDepth : Nat) (id : BindingId) :
    Except Diagnostic (CheckedAction signature) := do
  let expression ← select .action registry externalLevels signature maxDepth id
  return ⟨expression.term, expression.wellFormed⟩

end Silmaril.Logic.Temporal.TLA.DataElab.Endpoints
