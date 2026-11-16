module

public import Silmaril.Logic.CommonLogic.Core.FirstOrder.Defs
import Silmaril.Proofs.Logic.CommonLogic.FirstOrder

@[expose] public section

namespace Silmaril.Logic.CommonLogic.Core.FirstOrder

open Silmaril.Logic.Institution.Examples

theorem term_eval {S : Signature} {n k : Nat} {Γ : Fin n → Unit} {s : Unit}
    (M : Model S) (ρ : Fin n → M.Discourse) (σ : Fin k → List M.Discourse)
    (t : EQ.Term (signature S).toSignature Γ s) :
    (term t).eval M ρ σ = t.eval (model M).toAlgebra ρ :=
  Silmaril.Proofs.Logic.CommonLogic.FirstOrder.term_eval M ρ σ t

theorem formula_holds {S : Signature} {n k : Nat} {Γ : Fin n → Unit}
    (M : Model S) (ρ : Fin n → M.Discourse) (σ : Fin k → List M.Discourse)
    (p : FOL.Formula (signature S) Γ) :
    p.Holds (model M) ρ ↔ (formula p).Holds M ρ σ :=
  Silmaril.Proofs.Logic.CommonLogic.FirstOrder.formula_holds M p ρ σ

/-- Exact sentence meaning in the induced FOL model; this asserts no arbitrary-FOL expansion. -/
theorem sentence_holds {S : Signature} (M : Model S) (p : FOL.Sentence (signature S)) :
    p.Holds (model M) ↔ (room S).Sat M (formula (k := 0) p.formula) :=
  formula_holds M Fin.elim0 Fin.elim0 p.formula

/-- info: 'Silmaril.Logic.CommonLogic.Core.FirstOrder.formula_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms formula_holds
/-- info: 'Silmaril.Logic.CommonLogic.Core.FirstOrder.sentence_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sentence_holds

end Silmaril.Logic.CommonLogic.Core.FirstOrder
