module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseReplay

/-! # Stability and typed pullback of a single case-entry hoist -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay

open WithEntryLet (Site)

variable {Φ : Type v}

/-- The same address and hoisted syntax commute with value substitution. -/
theorem hoistAt_substVars (site : Site) (r : Region Φ) (θ : Nat → Tm Φ) :
    hoistAt site (r.substVars θ) = (hoistAt site r).map (·.substVars θ) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseReplay.hoistAt_substVars site r θ

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

/-- The addressed move retains the exact context and exit interface. -/
theorem hoistAt_exact (site : Site) (hr : HasType Γ r L) (hm : hoistAt site r = some s) :
    HasType Γ s L ∧ WithBoundEntryEta.Eqv Γ r s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseReplay.hoistAt_exact site hr hm

/-- Pull back a successful hoist to the same address before substitution. -/
theorem hoistAt_pullback (site : Site) (hr : HasType Γ r L) (θ : Nat → Tm Φ)
    (hm : hoistAt site (r.substVars θ) = some s) :
    ∃ q, hoistAt site r = some q ∧ s = q.substVars θ ∧
      HasType Γ q L ∧ WithBoundEntryEta.Eqv Γ r q L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseReplay.hoistAt_pullback site hr θ hm

/-- Guarded inputs keep constructor-valued branch arguments when rows
are moved into either case arm. -/
theorem hoistAt_guarded (site : Site) (hr : ValueBranches Γ r L) (hm : hoistAt site r = some s) :
    ValueBranches Γ s L ∧ WithBoundEntryEta.Eqv Γ r s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseReplay.hoistAt_guarded site hr hm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay
