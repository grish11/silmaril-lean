module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Assignments.Thms
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedRegularity

public section

/-!
# Quantitative carrier regularity for actual bounded extensional derivations

The carrier of every closed bounded derivation has an actual formation proof
with one additional level. Lookup formation needs no extra level. All members
of every cofinite family keep the same global budget throughout the proof;
actual typed assignment instantiates their explicitly sorted motives.

The empty theory is essential to these structural results. The name context
may be nonempty. This is a bound on actual derivations, not merely their
conclusions, and does not assert a bounded source-to-target proof map.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Every declaration has actual same-budget formation in the full bounded context. -/
theorem ECtx.JEqB.lookup_formation {levels : ℕ} {Γ : ECtx} {T t u : ETm 0}
    (h : ECtx.JEqB levels ∅ Γ T t u) {x : String} {A : ETm 0} (hx : Γ.Lookup x A) :
    ∃ n, n < levels ∧ ECtx.JEqB levels ∅ Γ (.univ n) A A :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedRegularity.lookup_formation h hx

/-- Every actual bounded judgment's carrier forms with at most one additional level. -/
theorem ECtx.JEqB.type_formation {levels : ℕ} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels ∅ Γ A a b) :
    ∃ n, n < levels + 1 ∧ ECtx.JEqB (levels + 1) ∅ Γ (.univ n) A A :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedRegularity.type_formation h

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
