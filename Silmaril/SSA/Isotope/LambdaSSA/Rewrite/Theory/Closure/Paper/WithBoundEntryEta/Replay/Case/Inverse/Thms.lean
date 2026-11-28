module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Inverse.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseInverse

/-! # Conditional inverse pullback for case hoisting -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay

open WithEntryLet (Site)

variable {Φ : Type v}

/-- A successful hoist uniquely determines its predecessor at that address. -/
theorem hoistAt_injective (site : Site) {p q r : Region Φ}
    (hp : hoistAt site p = some r) (hq : hoistAt site q = some r) : p = q :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseInverse.hoistAt_injective site hp hq

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {site : Site} {r : Region Φ}

/-- Reassemble the case and its common table before any substitution. -/
theorem CommonTableAt.predecessor (h : CommonTableAt Γ L site r) :
    ∃ q, HasType Γ q L ∧ hoistAt site q = some r :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseInverse.predecessor h

/-- Pull a witnessed backward step through one substitution when the
original has a shared typed table at the same address. The backward
equation uses the opt-in once-bound η theory. -/
theorem inverse_pullback (h : CommonTableAt Γ L site r) (θ : Nat → Tm Φ) {p : Region Φ}
    (step : hoistAt site p = some (r.substVars θ)) :
    ∃ q, hoistAt site q = some r ∧ p = q.substVars θ ∧
      HasType Γ q L ∧ WithBoundEntryEta.Eqv Γ r q L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseInverse.inverse_pullback h θ step

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay
