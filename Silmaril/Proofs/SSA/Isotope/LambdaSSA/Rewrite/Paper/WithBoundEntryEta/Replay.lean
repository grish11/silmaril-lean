module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Comparison.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Traversal.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Thms

/-! # Pulling back a single binary entry move -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Replay

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta (moveEntry₂ move₂)
open WithEntryLet (Site)
open Silmaril.DeBruijn (lift)

variable {Φ : Type v}

private theorem weaken_subst (r : Region Φ) (θ : Nat → Tm Φ) :
    (r.renameVars (lift Nat.succ)).substVars (Tm.liftSubst (Tm.liftSubst θ)) =
      (r.substVars (Tm.liftSubst θ)).renameVars (lift Nat.succ) := by
  rw [substVars_renameVars, renameVars_substVars, Tm.liftSubst_comp_lift_succ]

private theorem moveEntry₂_subst (r : Region Φ) (θ : Nat → Tm Φ) :
    moveEntry₂ (r.substVars θ) = (moveEntry₂ r).map (·.substVars θ) := by
  cases r with
  | cfg body n bs =>
    cases body <;> simp [moveEntry₂, Region.substVars, Tm.liftSubstN, weaken_subst]
  | _ => rfl

theorem move₂_substVars (site : Site) (r : Region Φ) (θ : Nat → Tm Φ) :
    move₂ site (r.substVars θ) = (move₂ site r).map (·.substVars θ) :=
  Site.rewriteAt_substVars moveEntry₂ moveEntry₂_subst site r θ

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]

private theorem moveEntry₁_exact {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : HasType Γ r L) (hm : Site.moveEntry r = some s) :
    HasType Γ s L ∧ WithBoundEntryEta.Eqv Γ r s L := by
  cases hr with
  | cfg R he hb =>
    cases he with
    | let₁ ha hd =>
      simp only [Site.moveEntry, Option.some.injEq] at hm
      subst s
      exact ⟨.let₁ ha (.cfg R hd (fun i => (hb i).renameVars ((Ren.wk _ _).lift (R i)))),
        WithBoundEntryEta.entryLet R ha hd hb⟩
    | _ => simp [Site.moveEntry] at hm
  | _ => simp [Site.moveEntry] at hm

theorem move₁_pullback (site : Site) {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : HasType Γ r L) (θ : Nat → Tm Φ)
    (hm : site.move (r.substVars θ) = some s) :
    ∃ q, site.move r = some q ∧ s = q.substVars θ ∧
      HasType Γ q L ∧ WithBoundEntryEta.Eqv Γ r q L := by
  rw [Site.move_substVars] at hm
  obtain ⟨q, he, rfl⟩ := Option.map_eq_some_iff.mp hm
  exact ⟨q, he, rfl, Site.rewriteAt_exact Site.moveEntry moveEntry₁_exact site hr he⟩

private theorem moveEntry₂_sound {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : HasType Γ r L) (hm : moveEntry₂ r = some s) :
    HasType Γ s L ∧ WithBoundEntryEta.Eqv Γ r s L := by
  cases hr with
  | cfg R he hb =>
    cases he with
    | let₂ ha hd =>
      simp only [moveEntry₂, Option.some.injEq] at hm
      subst s
      have hs := HasType.let₂ ha (.cfg R hd (fun i =>
        ((hb i).renameVars ((Ren.wk _ _).lift (R i))).renameVars ((Ren.wk _ _).lift (R i))))
      exact ⟨hs, WithBoundEntryEta.Comparison.entryLet₂ R ha hd hb⟩
    | _ => simp [moveEntry₂] at hm
  | _ => simp [moveEntry₂] at hm

private theorem move₂_sound (site : Site) {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : HasType Γ r L) (hm : move₂ site r = some s) :
    HasType Γ s L ∧ WithBoundEntryEta.Eqv Γ r s L :=
  Site.rewriteAt_exact moveEntry₂ moveEntry₂_sound site hr hm

theorem move₂_pullback (site : Site) {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : HasType Γ r L) (θ : Nat → Tm Φ)
    (hm : move₂ site (r.substVars θ) = some s) :
    ∃ q, move₂ site r = some q ∧ s = q.substVars θ ∧
      HasType Γ q L ∧ WithBoundEntryEta.Eqv Γ r q L := by
  rw [move₂_substVars] at hm
  obtain ⟨q, he, rfl⟩ := Option.map_eq_some_iff.mp hm
  exact ⟨q, he, rfl, move₂_sound site hr he⟩

private theorem moveEntry₂_guarded {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (hm : moveEntry₂ r = some s) :
    ValueBranches Γ s L ∧ WithBoundEntryEta.Eqv Γ r s L := by
  refine ⟨?_, (moveEntry₂_sound hr.hasType hm).2⟩
  cases hr with
  | cfg R he hb =>
    cases he with
    | let₂ ha hd =>
      simp only [moveEntry₂, Option.some.injEq] at hm
      subst s
      exact .let₂ ha (.cfg R hd (fun i =>
        ((hb i).renameVars ((Ren.wk _ _).lift (R i))).renameVars ((Ren.wk _ _).lift (R i))))
    | _ => simp [moveEntry₂] at hm
  | _ => simp [moveEntry₂] at hm

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType ofRegion sumIso)
open Paper.Extension.Singleton (projection projectStep iterateChosen)

variable {A D B : τ} {a : Tm Φ} {r s : Region Φ}

local notation "Seed" => WithBoundEntryEta.Step (τ := τ) (Φ := Φ)
local notation "Obj" => ofType (τ := τ) (Φ := Φ)

theorem repairTarget (site : Site) (ha : Tm.BranchValue [A] a D)
    (hr : ValueBranches [D] r [Silmaril.coprod B D])
    (f : Obj A ⟶ Obj B ⨿ Obj A)
    (hs : ValueBranches [A] s [Silmaril.coprod B D])
    (hm : move₂ site (r.substVars (Tm.singleSubst a ∘ lift Nat.succ)) = some s)
    (comm : f ≫ coprod.map (𝟙 (Obj B)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion hs ≫ (sumIso B D).hom) :
    let h := ofRegion (.br (ℓ := 0) rfl ha)
    ∃ g : Obj D ⟶ Obj B ⨿ Obj D,
      projectStep Seed g = projectStep Seed (ofRegion hr ≫ (sumIso B D).hom) ∧
      f ≫ coprod.map (𝟙 (Obj B)) h = h ≫ g := by
  obtain ⟨q, hsite, rfl, _, eq⟩ := move₂_pullback site hr.hasType _ hm
  have hq := (Site.rewriteAt_guarded moveEntry₂ moveEntry₂_guarded site hr hsite).1
  refine ⟨ofRegion hq ≫ (sumIso B D).hom, ?_, ?_⟩
  · have ec := (Paper.Extension.Singleton.ofRegion_eq_iff Seed hr hq).2 eq
    unfold projectStep
    simp only [Functor.map_comp]
    exact congrArg (fun k => (k ≫ (projection Seed).map (sumIso B D).hom) ≫ _) ec.symm
  · rwa [← Category.assoc, WithEntryLet.ofRegion_comp_constructor]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Replay
