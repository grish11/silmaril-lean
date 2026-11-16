module

public import Silmaril.Logic.Consequence.Refutation.CNF.Defs
public import Silmaril.Logic.Consequence.Refutation.Thms
import Silmaril.Proofs.Logic.Consequence.Refutation.CNF

/-!
# Clause entailment by CNF refutation: theorems

* `negSound`, `negComplete`: the unit clauses `cneg C` are exactly the negation of a clause
  without `0` (`lit_eval_neg`: `-l` complements `l` for `l ≠ 0`).
* `unsat_iff`: `Unsat csat Γ` is `CNF.Unsat` of the underlying CNF formula.
* `entails_iff_cnf_unsat`: `Γ` entails `C` iff `toCNF Γ ++ [[-l] | l ∈ C]` is `CNF.Unsat`.
* `entails_nil_iff_tauto`: the empty list entails `C` iff `C` has a complementary pair; this is
  SZS `TAU` of the monolithic problem `C` (`tauto_iff_tau`).
-/

@[expose] public section

namespace Silmaril.Consequence.Refutation.CNF

open Silmaril.Logic.SAT

theorem lit_eval_neg (τ : Assignment) {l : Lit} (h : l ≠ 0) :
    Lit.eval τ (-l) = !Lit.eval τ l :=
  Proofs.Logic.Consequence.Refutation.CNF.lit_eval_neg τ h

theorem toCNF_cneg (C : WClause) : toCNF (cneg C) = C.1.map fun l => [-l] :=
  Proofs.Logic.Consequence.Refutation.CNF.toCNF_cneg C

theorem negSound : NegSound csat cneg := Proofs.Logic.Consequence.Refutation.CNF.negSound

theorem negComplete : NegComplete csat cneg :=
  Proofs.Logic.Consequence.Refutation.CNF.negComplete

theorem unsat_iff (Γ : List WClause) : Unsat csat Γ ↔ CNF.Unsat (toCNF Γ) :=
  Proofs.Logic.Consequence.Refutation.CNF.unsat_iff Γ

/-- Clause entailment is unsatisfiability of the premises with the negated clause. -/
theorem entails_iff_cnf_unsat (Γ : List WClause) (C : WClause) :
    Entails csat Γ C ↔ CNF.Unsat (toCNF Γ ++ C.1.map fun l => [-l]) := by
  rw [entails_iff_unsat negSound negComplete, unsat_iff, ← toCNF_cneg]
  simp [toCNF]

theorem entails_nil_iff_tauto (C : WClause) : Entails csat [] C ↔ Tauto C.1 :=
  Proofs.Logic.Consequence.Refutation.CNF.entails_nil_iff_tauto C

theorem tauto_iff_tau (C : WClause) :
    Tauto C.1 ↔ Logic.Szs.Current.TAU (Logic.Szs.Problem.monolithic {τ | csat τ C}) := by
  rw [← entails_nil_iff_tauto]
  exact ⟨fun h => ⟨rfl, Set.eq_univ_of_forall fun τ => h τ (by simp [SatAll])⟩,
    fun h τ _ => (Set.eq_univ_iff_forall.1 h.2 τ : τ ∈ {τ | csat τ C})⟩

end Silmaril.Consequence.Refutation.CNF
