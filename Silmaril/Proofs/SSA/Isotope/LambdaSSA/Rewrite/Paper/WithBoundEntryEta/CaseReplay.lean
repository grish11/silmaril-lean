module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Generators.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Traversal.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

/-! # Exact pullback of a single case-entry move -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseReplay

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay
open WithBoundEntryEta.Generators (weakenRows)
open WithEntryLet (Site)

variable {Φ : Type v}

private theorem hoistRoot_subst (r : Region Φ) (θ : Nat → Tm Φ) :
    hoistRoot (r.substVars θ) = (hoistRoot r).map (·.substVars θ) := by
  cases r with
  | cfg e n rows =>
    cases e with
    | case a l r =>
      have hw : weakenRows (fun j => (rows j).substVars (Tm.liftSubst θ)) =
          (fun j => ((weakenRows rows) j).substVars (Tm.liftSubst (Tm.liftSubst θ))) := by
        funext j
        simp only [weakenRows, substVars_renameVars, renameVars_substVars,
          Tm.liftSubst_comp_lift_succ]
      simp only [hoistRoot, Region.substVars, Option.map_some, hw]
    | _ => rfl
  | _ => rfl

theorem hoistAt_substVars (site : Site) (r : Region Φ) (θ : Nat → Tm Φ) :
    hoistAt site (r.substVars θ) = (hoistAt site r).map (·.substVars θ) :=
  Site.rewriteAt_substVars hoistRoot hoistRoot_subst site r θ

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

private theorem hoistRoot_exact (hr : HasType Γ r L) (hm : hoistRoot r = some s) :
    HasType Γ s L ∧ WithBoundEntryEta.Eqv Γ r s L := by
  cases hr with
  | cfg R he hb =>
    cases he with
    | case ha hl hr =>
      simp only [hoistRoot, Option.some.injEq] at hm
      subst s
      refine ⟨.case ha (.cfg R hl ?_) (.cfg R hr ?_), WithBoundEntryEta.Generators.caseEntry R ha hl hr hb⟩
      all_goals exact fun j => (hb j).renameVars ((Ren.wk _ _).lift (R j))
    | _ => simp [hoistRoot] at hm
  | _ => simp [hoistRoot] at hm

theorem hoistAt_exact (site : Site) (hr : HasType Γ r L) (hm : hoistAt site r = some s) :
    HasType Γ s L ∧ WithBoundEntryEta.Eqv Γ r s L :=
  Site.rewriteAt_exact hoistRoot hoistRoot_exact site hr hm

theorem hoistAt_pullback (site : Site) (hr : HasType Γ r L) (θ : Nat → Tm Φ)
    (hm : hoistAt site (r.substVars θ) = some s) :
    ∃ q, hoistAt site r = some q ∧ s = q.substVars θ ∧
      HasType Γ q L ∧ WithBoundEntryEta.Eqv Γ r q L := by
  rw [hoistAt_substVars] at hm
  obtain ⟨q, he, rfl⟩ := Option.map_eq_some_iff.mp hm
  exact ⟨q, he, rfl, hoistAt_exact site hr he⟩

private theorem hoistRoot_guarded (hr : ValueBranches Γ r L) (hm : hoistRoot r = some s) :
    ValueBranches Γ s L ∧ WithBoundEntryEta.Eqv Γ r s L := by
  refine ⟨?_, (hoistRoot_exact hr.hasType hm).2⟩
  cases hr with
  | cfg R he hb =>
    cases he with
    | case ha hl hr =>
      simp only [hoistRoot, Option.some.injEq] at hm
      subst s
      exact .case ha (.cfg R hl (fun j => (hb j).renameVars ((Ren.wk _ _).lift (R j))))
        (.cfg R hr (fun j => (hb j).renameVars ((Ren.wk _ _).lift (R j))))
    | _ => simp [hoistRoot] at hm
  | _ => simp [hoistRoot] at hm

theorem hoistAt_guarded (site : Site) (hr : ValueBranches Γ r L) (hm : hoistAt site r = some s) :
    ValueBranches Γ s L ∧ WithBoundEntryEta.Eqv Γ r s L :=
  Site.rewriteAt_guarded hoistRoot hoistRoot_guarded site hr hm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseReplay
