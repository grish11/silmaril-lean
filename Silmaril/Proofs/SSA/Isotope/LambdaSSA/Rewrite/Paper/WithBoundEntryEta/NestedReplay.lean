module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Nested.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Generators.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Traversal.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

/-! # Substitution and exact pullback for nested-entry hoisting -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplay

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NestedReplay
open WithEntryLet (Site)
open Silmaril.DeBruijn (lift)

variable {Φ : Type v}

theorem map_cfgEntryContinuations {n : Nat} (outer : Fin n → Region Φ) (θ : Nat → Tm Φ) :
    mapLSubstVars θ (cfgEntryContinuations outer) =
      cfgEntryContinuations (fun j => (outer j).substVars (Tm.liftSubst θ)) := by
  funext i
  change Region.cfg (.br i (.var 0)) n
      (fun j => ((outer j).renameVars (lift Nat.succ)).substVars (Tm.liftSubst (Tm.liftSubst θ))) =
    .cfg (.br i (.var 0)) n
      (fun j => ((outer j).substVars (Tm.liftSubst θ)).renameVars (lift Nat.succ))
  congr 1
  funext j
  exact congrFun (mapLSubstVars_liftVars (fun _ => outer j) θ) 0

/-- The one root equation commutes with substitution also under a
nonempty inner label binder and each inner row's payload. -/
private theorem hoistRoot_subst (r : Region Φ) (θ : Nat → Tm Φ) :
    hoistRoot (r.substVars θ) = (hoistRoot r).map (·.substVars θ) := by
  cases r with
  | cfg e n outer =>
    cases e with
    | cfg e m inner =>
      simp only [hoistRoot, Region.substVars, Option.map_some, substVars_lsubst, map_cfgEntryContinuations]
    | _ => rfl
  | _ => rfl

theorem hoistAt_substVars (site : Site) (r : Region Φ) (θ : Nat → Tm Φ) :
    hoistAt site (r.substVars θ) = (hoistAt site r).map (·.substVars θ) :=
  Site.rewriteAt_substVars hoistRoot hoistRoot_subst site r θ

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

theorem liftedReentry_hasType {m n : Nat} {Γ : VCtx τ} {L : LCtx τ}
    {outer : Fin n → Region Φ} (S : Fin m → τ) (R : Fin n → τ)
    (ho : ∀ j, HasType (R j :: Γ) (outer j) (List.ofFn R ++ L)) :
    LSubst.HasType Γ (List.ofFn S ++ (List.ofFn R ++ L)) (List.ofFn S ++ L)
      (liftLSubstN m (cfgEntryContinuations outer)) := by
  simpa only [List.length_ofFn] using (cfgEntryContinuations_hasType R ho).append (List.ofFn S)

private theorem hoistRoot_exact (hr : HasType Γ r L) (hm : hoistRoot r = some s) :
    HasType Γ s L ∧ WithBoundEntryEta.Eqv Γ r s L := by
  cases hr with
  | cfg R he ho =>
    cases he with
    | cfg S he hi =>
      simp only [hoistRoot, Option.some.injEq] at hm
      subst s
      have family := liftedReentry_hasType S R ho
      exact ⟨.cfg S (he.lsubst family) (fun j => (hi j).lsubst (family.liftVars (S j))),
        WithBoundEntryEta.Generators.nested S R he hi ho⟩
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
  | cfg R he ho =>
    cases he with
    | cfg S he hi =>
      simp only [hoistRoot, Option.some.injEq] at hm
      subst s
      apply (ValueBranches.cfg S he hi).lsubst
      intro i A h
      exact .cfg R (.br h (.var rfl))
        (fun j => (ho j).renameVars ((Ren.wk _ A).lift (R j)))
    | _ => simp [hoistRoot] at hm
  | _ => simp [hoistRoot] at hm

theorem hoistAt_guarded (site : Site) (hr : ValueBranches Γ r L) (hm : hoistAt site r = some s) :
    ValueBranches Γ s L ∧ WithBoundEntryEta.Eqv Γ r s L :=
  Site.rewriteAt_guarded hoistRoot hoistRoot_guarded site hr hm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplay
