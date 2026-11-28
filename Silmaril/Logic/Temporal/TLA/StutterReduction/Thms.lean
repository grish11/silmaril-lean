module

public import Silmaril.Logic.Temporal.TLA.StutterReduction.Defs
public import Silmaril.Logic.Temporal.TLA.Thms
import Silmaril.Proofs.Logic.Temporal.TLA.StutterReduction.Canonical

public section

namespace Silmaril.Logic.Temporal.TLA

universe u v

variable {S : Type u}

namespace Behavior

/-- The stream-valued reduction satisfies all three clauses of Lamport's equation (48). -/
theorem canonicalReduction_eq48 : SatisfiesLamport48 (S := S) canonicalReduction :=
  Proofs.Logic.Temporal.TLA.StutterReduction.canonicalReduction_eq48

/-- Equation (48) determines the reduction on all behaviors. -/
theorem eq_canonicalReduction_of_eq48 {reduce : Behavior S → Behavior S}
    (h : SatisfiesLamport48 reduce) : reduce = canonicalReduction :=
  Proofs.Logic.Temporal.TLA.StutterReduction.eq_canonicalReduction_of_eq48 h

theorem canonicalReduction_retime (σ : Behavior S) (r : Retiming) :
    (σ.retime r).canonicalReduction = σ.canonicalReduction :=
  Proofs.Logic.Temporal.TLA.StutterReduction.canonicalReduction_retime σ r

/-- A behavior whose repetitions lie in its constant tail is already reduced. -/
theorem canonicalReduction_of_reduced (σ : Behavior S)
    (h : ∀ i, σ (i + 1) = σ i → ∀ j, i ≤ j → σ j = σ i) :
    σ.canonicalReduction = σ :=
  Proofs.Logic.Temporal.TLA.StutterReduction.canonicalReduction_of_reduced σ h

/-- Equality of Lamport reductions is exactly common-expansion stuttering equivalence. -/
theorem canonicalReduction_eq_iff_stutterEquiv (σ τ : Behavior S) :
    σ.canonicalReduction = τ.canonicalReduction ↔ StutterEquiv σ τ :=
  Proofs.Logic.Temporal.TLA.StutterReduction.canonicalReduction_eq_iff_stutterEquiv σ τ

end Behavior

/-- Lamport's equation (49) on product states. The witness `ρ` has the same
full-state reduction as `σ`; `τ` agrees with `ρ` away from the hidden component. -/
theorem hide_iff_lamport_reduction {V : Type v} {p : Behavior (S × V) → Prop}
    (hp : StutterInvariant p) (σ : Behavior (S × V)) :
    hide p (σ.map Prod.fst) ↔
      ∃ ρ τ : Behavior (S × V),
        σ.canonicalReduction = ρ.canonicalReduction ∧ ρ.map Prod.fst = τ.map Prod.fst ∧ p τ := by
  simpa only [Behavior.canonicalReduction_eq_iff_stutterEquiv] using hide_iff_lamport hp σ

/-- A product-state formula binder satisfies Lamport's canonical reduction clause. -/
theorem Formula.sat_existsFlex_iff_lamport_reduction {V : Type u} (p : Formula (S × V))
    (σ : Behavior (S × V)) :
    (Formula.existsFlex p).Sat (σ.map Prod.fst) ↔
      ∃ ρ τ : Behavior (S × V),
        σ.canonicalReduction = ρ.canonicalReduction ∧ ρ.map Prod.fst = τ.map Prod.fst ∧ p.Sat τ :=
  (sat_existsFlex p _).trans (hide_iff_lamport_reduction p.sat_stutterInvariant σ)

end Silmaril.Logic.Temporal.TLA
