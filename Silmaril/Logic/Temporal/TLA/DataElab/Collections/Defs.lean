module

public import Silmaril.Logic.Temporal.TLA.DataElab.Endpoints.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Endpoints.Defs

/-! Level-checked lowering for the TLA+ collection fragment. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Collections

open Resolution

universe u

/-- Select a closed constant- or state-level definition in the checked registry.
In addition to the core data forms, admit grouped and tuple binders, bounded
functions, records, function and record sets, graph access, tuples and EXCEPT. -/
public def lowerState (registry : CheckedRegistry) (externalLevels : Levels.ExternalLevels)
    (signature : ExternalSignature) (maxDepth : Nat) (id : BindingId) :
    Except Endpoints.Diagnostic (CheckedExpr signature .collections) :=
  Endpoints.lowerStateIn registry externalLevels signature .collections maxDepth id

/-- A closed action-level expansion in the collection fragment. -/
public structure CheckedAction (signature : ExternalSignature) where
  private mk ::
  expression : CheckedExpr signature .collections

/-- Check the exact registry and select a closed collection action. -/
public def lowerAction (registry : CheckedRegistry) (externalLevels : Levels.ExternalLevels)
    (signature : ExternalSignature) (maxDepth : Nat) (id : BindingId) :
    Except Endpoints.Diagnostic (CheckedAction signature) := do
  return ⟨← Endpoints.select .action registry externalLevels signature .collections maxDepth id⟩

@[expose] public noncomputable def CheckedAction.eval {V : Type u} {signature : ExternalSignature}
    (action : CheckedAction signature) (ops : CollectionOperations V) (B : Booleans V)
    (external : ExternalInterpretation V signature) (endpoints : Endpoints.EndpointValuation V) : V :=
  action.expression.term.eval ops B external ⟨endpoints.rigid, endpoints.source⟩
    (fun _ => ops.enum []) endpoints.target

end Silmaril.Logic.Temporal.TLA.DataElab.Collections
