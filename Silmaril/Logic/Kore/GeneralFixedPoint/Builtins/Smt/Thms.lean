module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Source
import Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Translation
import Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins.Smt.RawAdequacy

-- Builtin names are configurable despite the canonical fallback instance.
set_option linter.concreteInstances false
@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
open Silmaril.Logic.Smt

theorem compile_correct {s : ValueSort} (p : Pattern s) (v : Valuation) :
    ∀ {k : Nat} {Γ : Fin k → Uflia.SortCode Empty}
      (values : ∀ i, (target v).carriers.value (Γ i))
      (out : Uflia.Quantified.Term signature Γ s.code),
    Uflia.Quantified.Formula.Holds (p.compile out) (target v) values ↔
      Uflia.Quantified.eval (target v) values out ∈ p.denote v :=
  Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins.Smt.compile_correct p v

/-- Successful raw checking agrees with the independent original interpreter
for every actual builtin model and legal finite set-valued environment. -/
theorem rawAdequacy [SortBindings] : Task.rawAdequacy :=
  Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins.Smt.rawAdequacy_task

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
