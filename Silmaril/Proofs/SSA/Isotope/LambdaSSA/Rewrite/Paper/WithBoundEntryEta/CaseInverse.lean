module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Inverse.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Traversal.Thms

/-! # Read back an addressed case hoist from a common typed table -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseInverse

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open WithBoundEntryEta.CaseReplay
open WithBoundEntryEta.Generators (weakenRows)
open WithEntryLet (Site)
open Silmaril.DeBruijn (lift)

variable {Φ : Type v}

/-- A syntactic readback used only on known outputs of a hoist. -/
private def readbackRoot : Region Φ → Option (Region Φ)
  | .case a (.cfg l n rows) (.cfg r _ _) =>
    some (.cfg (.case a l r) n (fun j => (rows j).renameVars (lift Nat.pred)))
  | _ => none

private theorem readbackRoot_undo {p r : Region Φ} (h : hoistRoot p = some r) :
    readbackRoot r = some p := by
  cases p with
  | cfg e n rows =>
    cases e with
    | case a l r =>
      simp only [hoistRoot, Option.some.injEq] at h
      rw [← h]
      have cancel : (lift Nat.pred ∘ lift Nat.succ) = id := by
        funext i
        cases i <;> rfl
      have recover : (fun j => ((weakenRows rows) j).renameVars (lift Nat.pred)) = rows := by
        funext j
        simp only [weakenRows, renameVars_comp, cancel, renameVars_id]
      simp only [readbackRoot, recover]
    | _ => contradiction
  | _ => contradiction

theorem hoistAt_injective (site : Site) {p q r : Region Φ}
    (hp : hoistAt site p = some r) (hq : hoistAt site q = some r) : p = q := by
  have hp' := Site.rewriteAt_undo hoistRoot readbackRoot readbackRoot_undo site hp
  have hq' := Site.rewriteAt_undo hoistRoot readbackRoot readbackRoot_undo site hq
  exact Option.some.inj (hp'.symm.trans hq')

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {site : Site} {r : Region Φ}

theorem predecessor (h : CommonTableAt Γ L site r) :
    ∃ q, HasType Γ q L ∧ hoistAt site q = some r := by
  induction h with
  | here R ha hl hr hb =>
    exact ⟨_, .cfg R (.case ha hl hr) hb, rfl⟩
  | unaryBody ha _ ih =>
    obtain ⟨q, ht, hm⟩ := ih
    refine ⟨.let₁ _ q, .let₁ ha ht, ?_⟩
    simp only [hoistAt, Site.rewriteAt, hm, Option.map_some]
  | binaryBody ha _ ih =>
    obtain ⟨q, ht, hm⟩ := ih
    refine ⟨.let₂ _ q, .let₂ ha ht, ?_⟩
    simp only [hoistAt, Site.rewriteAt, hm, Option.map_some]
  | leftArm ha _ hr ih =>
    obtain ⟨q, ht, hm⟩ := ih
    refine ⟨.case _ q _, .case ha ht hr, ?_⟩
    simp only [hoistAt, Site.rewriteAt, hm, Option.map_some]
  | rightArm ha hl _ ih =>
    obtain ⟨q, ht, hm⟩ := ih
    refine ⟨.case _ _ q, .case ha hl ht, ?_⟩
    simp only [hoistAt, Site.rewriteAt, hm, Option.map_some]
  | entry R _ hb ih =>
    obtain ⟨q, ht, hm⟩ := ih
    refine ⟨.cfg q _ _, .cfg R ht hb, ?_⟩
    simp only [hoistAt, Site.rewriteAt, hm, Option.map_some]
  | @block Γ L site n e rows R i he hb body ih =>
    obtain ⟨q, ht, hm⟩ := ih
    refine ⟨.cfg e n (Function.update rows i q), .cfg R he ?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · subst j
        simpa only [Function.update_self] using ht
      · simpa only [Function.update_of_ne hj] using hb j hj
    · simp only [hoistAt, Site.rewriteAt, i.isLt, dite_true, Function.update_self, hm, Option.map_some,
        Function.update_idem, Function.update_eq_self]

theorem inverse_pullback (h : CommonTableAt Γ L site r) (θ : Nat → Tm Φ) {p : Region Φ}
    (step : hoistAt site p = some (r.substVars θ)) :
    ∃ q, hoistAt site q = some r ∧ p = q.substVars θ ∧
      HasType Γ q L ∧ WithBoundEntryEta.Eqv Γ r q L := by
  obtain ⟨q, ht, hm⟩ := predecessor h
  have specialized : hoistAt site (q.substVars θ) = some (r.substVars θ) := by
    rw [hoistAt_substVars, hm]
    rfl
  exact ⟨q, hm, hoistAt_injective site step specialized, ht, (hoistAt_exact site ht hm).2.symm⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseInverse
