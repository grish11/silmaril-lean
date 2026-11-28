module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Script.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplay

/-! # Typed forward execution and pullback through one substitution -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.ScriptReplay

variable {Φ : Type v}

/-- Substitution preserves the success or failure of the whole script. -/
theorem run_substVars (moves : List Move) (r : Region Φ) (θ : Nat → Tm Φ) :
    run moves (r.substVars θ) = (run moves r).map (·.substVars θ) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplay.run_substVars moves r θ

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {Γ Δ : VCtx τ} {L : LCtx τ} {moves : List Move} {r s : Region Φ}

theorem Trace.run_eq (h : Trace Γ L moves r s) : run moves r = some s :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplay.trace_run h

theorem Trace.typed (h : Trace Γ L moves r s) : HasType Γ r L ∧ HasType Γ s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplay.trace_typed h

/-- The chain proves equality in the opt-in once-bound η relation. -/
theorem Trace.eqv (h : Trace Γ L moves r s) : WithBoundEntryEta.Eqv Γ r s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplay.trace_eqv h

/-- A typed substitution preserves each intermediate typing and applies
the same action at the same address. -/
theorem Trace.substVars (h : Trace Γ L moves r s) {θ : Nat → Tm Φ}
    (hθ : ∀ i A, At Γ i A → Tm.HasType Δ (θ i) A) :
    Trace Δ L moves (r.substVars θ) (s.substVars θ) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplay.trace_substVars h hθ

/-- Pull back a successful forward script to the identical sequence of
actions and addresses on the original region. The proof uses the same
substitution at every intermediate region. -/
theorem run_pullback (hr : HasType Γ r L) (θ : Nat → Tm Φ)
    (h : run moves (r.substVars θ) = some s) :
    ∃ q, Trace Γ L moves r q ∧ s = q.substVars θ :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplay.run_pullback hr θ h

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.ScriptReplay
