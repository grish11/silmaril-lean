module

public import Silmaril.Logic.Temporal.TLA.DataElab.Endpoints.Defs

/-! Evaluation equations for whole-operand prime and diagonal endpoints. -/

public section

namespace Silmaril.Logic.Temporal.TLA.DataElab

open Resolution

universe u
variable {V : Type u} {signature : ExternalSignature}

theorem Term.eval_prime (ops : DataOperations V) (B : Booleans V)
    (external : ExternalInterpretation V signature) (valuation : Valuation V)
    (site : Site) (operand : Term signature) (witnesses : Nat → V) (target : BindingId → V) :
    (Term.prime site operand).eval ops B external valuation witnesses target =
      operand.eval ops B external { valuation with flexible := target } witnesses target := rfl

namespace Endpoints

theorem CheckedAction.eval_diagonal (action : CheckedAction signature) (ops : DataOperations V)
    (B : Booleans V) (external : ExternalInterpretation V signature) (valuation : Valuation V) :
    action.eval ops B external ⟨valuation.rigid, valuation.flexible, valuation.flexible⟩ =
      action.term.eval ops B external valuation (fun _ => ops.enum []) := by
  cases valuation
  rfl

end Endpoints
end Silmaril.Logic.Temporal.TLA.DataElab
