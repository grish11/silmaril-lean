module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Script.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Branch.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Nested.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

/-! # Exact replay of a finite chain of addressed generators -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplay

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open WithBoundEntryEta.ScriptReplay
open WithEntryLet (Site)

variable {Φ : Type v}

private theorem apply_substVars (move : Move) (r : Region Φ) (θ : Nat → Tm Φ) :
    move.apply (r.substVars θ) = (move.apply r).map (·.substVars θ) := by
  cases move with
  | bindBranch site => exact WithBoundEntryEta.BranchReplay.bindAt_substVars site r θ
  | unaryEntry site => exact Site.move_substVars site r θ
  | binaryEntry site => exact WithBoundEntryEta.move₂_substVars site r θ
  | caseEntry site => exact WithBoundEntryEta.CaseReplay.hoistAt_substVars site r θ
  | nestedEntry site => exact WithBoundEntryEta.NestedReplay.hoistAt_substVars site r θ

theorem run_substVars (moves : List Move) (r : Region Φ) (θ : Nat → Tm Φ) :
    run moves (r.substVars θ) = (run moves r).map (·.substVars θ) := by
  induction moves generalizing r with
  | nil => rfl
  | cons move rest ih =>
    simp only [run, apply_substVars]
    cases move.apply r with
    | none => rfl
    | some q => exact ih q

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {Γ Δ : VCtx τ} {L : LCtx τ} {moves : List Move} {r s : Region Φ}

private theorem move_pullback (move : Move) (hr : HasType Γ r L) (θ : Nat → Tm Φ)
    (h : move.apply (r.substVars θ) = some s) :
    ∃ q, move.apply r = some q ∧ s = q.substVars θ ∧ HasType Γ q L ∧ WithBoundEntryEta.Eqv Γ r q L := by
  cases move with
  | bindBranch site => exact WithBoundEntryEta.BranchReplay.bindAt_pullback site hr θ h
  | unaryEntry site => exact WithBoundEntryEta.move₁_pullback site hr θ h
  | binaryEntry site => exact WithBoundEntryEta.move₂_pullback site hr θ h
  | caseEntry site => exact WithBoundEntryEta.CaseReplay.hoistAt_pullback site hr θ h
  | nestedEntry site => exact WithBoundEntryEta.NestedReplay.hoistAt_pullback site hr θ h

theorem trace_run (h : Trace Γ L moves r s) : run moves r = some s := by
  induction h with
  | nil => rfl
  | cons _ step _ ih =>
    rw [run, step]
    exact ih

theorem trace_typed (h : Trace Γ L moves r s) : HasType Γ r L ∧ HasType Γ s L := by
  induction h with
  | nil hr => exact ⟨hr, hr⟩
  | cons hr _ _ ih => exact ⟨hr, ih.2⟩

theorem trace_eqv (h : Trace Γ L moves r s) : WithBoundEntryEta.Eqv Γ r s L := by
  induction h with
  | nil hr => exact .paper (.refl hr)
  | @cons move _ r next _ hr step _ ih =>
    have h : move.apply (r.substVars Tm.var) = some next := by
      simpa only [Region.substVars_var] using step
    obtain ⟨q, _, he, _, eq⟩ := move_pullback move hr Tm.var h
    simp only [Region.substVars_var] at he
    cases he
    exact eq.trans ih

theorem trace_substVars (h : Trace Γ L moves r s) {θ : Nat → Tm Φ}
    (hθ : ∀ i A, At Γ i A → Tm.HasType Δ (θ i) A) :
    Trace Δ L moves (r.substVars θ) (s.substVars θ) := by
  induction h with
  | nil hr => exact .nil (hr.substVars hθ)
  | cons hr step _ ih =>
    exact .cons (hr.substVars hθ) (by simp only [apply_substVars, step, Option.map_some]) ih

theorem run_pullback (hr : HasType Γ r L) (θ : Nat → Tm Φ)
    (h : run moves (r.substVars θ) = some s) :
    ∃ q, Trace Γ L moves r q ∧ s = q.substVars θ := by
  induction moves generalizing r s with
  | nil => exact ⟨r, .nil hr, (Option.some.inj h).symm⟩
  | cons move rest ih =>
    cases he : move.apply (r.substVars θ) with
    | none => simp [run, he] at h
    | some next =>
      obtain ⟨q, hq, rfl, ht, _⟩ := move_pullback move hr θ he
      have tail : run rest (q.substVars θ) = some s := by
        rw [run, he] at h
        exact h
      obtain ⟨out, htrace, heq⟩ := ih ht tail
      exact ⟨out, .cons hr hq htrace, heq⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplay
