module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Defs

/-! # Substitution and guarded typing for addressed region rewrites -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetTraversal

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open WithEntryLet (Site)

variable {Φ : Type v}

theorem rewriteAt_substVars (root : Region Φ → Option (Region Φ))
    (natural : ∀ r θ, root (r.substVars θ) = (root r).map (·.substVars θ))
    (site : Site) (r : Region Φ) (θ : Nat → Tm Φ) :
    site.rewriteAt root (r.substVars θ) = (site.rewriteAt root r).map (·.substVars θ) := by
  induction site generalizing r θ with
  | here => exact natural r θ
  | unaryBody next ih | binaryBody next ih | leftArm next ih | rightArm next ih | entry next ih =>
    cases r <;> simp [Site.rewriteAt, Region.substVars, ih, Option.map_map, Function.comp_def]
  | block i next ih =>
    cases r with
    | cfg e n bs =>
      simp only [Site.rewriteAt, Region.substVars]
      by_cases hi : i < n
      · simp only [hi, dite_true, ih, Option.map_map, Function.comp_def]
        apply congrArg (fun k => (next.rewriteAt root (bs ⟨i, hi⟩)).map k)
        funext b
        apply congrArg (Region.cfg (e.substVars θ) n)
        funext j
        by_cases h : j = ⟨i, hi⟩ <;> simp [h]
      · simp only [hi, dite_false, Option.map_none]
    | _ => rfl

theorem rewriteAt_undo (forward backward : Region Φ → Option (Region Φ))
    (undo : ∀ {r s}, forward r = some s → backward s = some r)
    (site : Site) {r s : Region Φ} (h : site.rewriteAt forward r = some s) :
    site.rewriteAt backward s = some r := by
  induction site generalizing r s with
  | here => exact undo h
  | unaryBody next ih | binaryBody next ih | leftArm next ih | rightArm next ih | entry next ih =>
    cases r <;> simp only [Site.rewriteAt] at h
    all_goals try contradiction
    obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Site.rewriteAt, ih hbody, Option.map_some]
  | block i next ih =>
    cases r with
    | cfg e n rows =>
      simp only [Site.rewriteAt] at h
      split at h
      next hi =>
        obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [Site.rewriteAt, hi, dite_true, Function.update_self, ih hbody, Option.map_some,
          Function.update_idem, Function.update_eq_self]
      next _ => contradiction
    | _ => contradiction

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

theorem rewriteAt_guarded (root : Region Φ → Option (Region Φ))
    (sound : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s}, ValueBranches Γ r L → root r = some s →
      ValueBranches Γ s L ∧ Extension.Eqv Seed Γ r s L)
    (site : Site) {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (hm : site.rewriteAt root r = some s) :
    ValueBranches Γ s L ∧ Extension.Eqv Seed Γ r s L := by
  induction site generalizing Γ L r s with
  | here => exact sound hr hm
  | unaryBody next ih =>
    cases hr with
    | let₁ ha hb =>
      simp only [Site.rewriteAt] at hm
      obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hm
      obtain ⟨ht, eq⟩ := ih hb hbody
      exact ⟨.let₁ ha ht, .let₁ ha eq⟩
    | _ => simp [Site.rewriteAt] at hm
  | binaryBody next ih =>
    cases hr with
    | let₂ ha hb =>
      simp only [Site.rewriteAt] at hm
      obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hm
      obtain ⟨ht, eq⟩ := ih hb hbody
      exact ⟨.let₂ ha ht, .let₂ ha eq⟩
    | _ => simp [Site.rewriteAt] at hm
  | leftArm next ih =>
    cases hr with
    | case ha hl hr =>
      simp only [Site.rewriteAt] at hm
      obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hm
      obtain ⟨ht, eq⟩ := ih hl hbody
      exact ⟨.case ha ht hr, .case ha eq (.paper (.refl hr.hasType))⟩
    | _ => simp [Site.rewriteAt] at hm
  | rightArm next ih =>
    cases hr with
    | case ha hl hr =>
      simp only [Site.rewriteAt] at hm
      obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hm
      obtain ⟨ht, eq⟩ := ih hr hbody
      exact ⟨.case ha hl ht, .case ha (.paper (.refl hl.hasType)) eq⟩
    | _ => simp [Site.rewriteAt] at hm
  | entry next ih =>
    cases hr with
    | cfg R he hb =>
      simp only [Site.rewriteAt] at hm
      obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hm
      obtain ⟨ht, eq⟩ := ih he hbody
      exact ⟨.cfg R ht hb, .cfg R eq (fun i => .paper (.refl (hb i).hasType))⟩
    | _ => simp [Site.rewriteAt] at hm
  | block i next ih =>
    cases hr with
    | cfg R he hb =>
      simp only [Site.rewriteAt] at hm
      split at hm
      next hi =>
        obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hm
        obtain ⟨ht, eq⟩ := ih (hb ⟨i, hi⟩) hbody
        refine ⟨.cfg R he ?_, .cfg R (.paper (.refl he.hasType)) ?_⟩
        · intro j
          by_cases h : j = ⟨i, hi⟩
          · subst j
            simpa using ht
          · simpa [Function.update_apply, h] using hb j
        · intro j
          by_cases h : j = ⟨i, hi⟩
          · subst j
            simpa using eq
          · simpa [Function.update_apply, h] using
              (Paper.Extension.Eqv.paper (Seed := Seed) (.refl (hb j).hasType))
      next _ => contradiction
    | _ => simp [Site.rewriteAt] at hm
theorem rewriteAt_exact (root : Region Φ → Option (Region Φ))
    (sound : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s}, HasType Γ r L → root r = some s →
      HasType Γ s L ∧ Extension.Eqv Seed Γ r s L)
    (site : Site) {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : HasType Γ r L) (hm : site.rewriteAt root r = some s) :
    HasType Γ s L ∧ Extension.Eqv Seed Γ r s L := by
  induction site generalizing Γ L r s with
  | here => exact sound hr hm
  | unaryBody next ih =>
    cases hr with
    | let₁ ha hb =>
      simp only [Site.rewriteAt] at hm
      obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hm
      obtain ⟨ht, eq⟩ := ih hb hbody
      exact ⟨.let₁ ha ht, .let₁ ha eq⟩
    | _ => simp [Site.rewriteAt] at hm
  | binaryBody next ih =>
    cases hr with
    | let₂ ha hb =>
      simp only [Site.rewriteAt] at hm
      obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hm
      obtain ⟨ht, eq⟩ := ih hb hbody
      exact ⟨.let₂ ha ht, .let₂ ha eq⟩
    | _ => simp [Site.rewriteAt] at hm
  | leftArm next ih =>
    cases hr with
    | case ha hl hr =>
      simp only [Site.rewriteAt] at hm
      obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hm
      obtain ⟨ht, eq⟩ := ih hl hbody
      exact ⟨.case ha ht hr, .case ha eq (.paper (.refl hr))⟩
    | _ => simp [Site.rewriteAt] at hm
  | rightArm next ih =>
    cases hr with
    | case ha hl hr =>
      simp only [Site.rewriteAt] at hm
      obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hm
      obtain ⟨ht, eq⟩ := ih hr hbody
      exact ⟨.case ha hl ht, .case ha (.paper (.refl hl)) eq⟩
    | _ => simp [Site.rewriteAt] at hm
  | entry next ih =>
    cases hr with
    | cfg R he hb =>
      simp only [Site.rewriteAt] at hm
      obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hm
      obtain ⟨ht, eq⟩ := ih he hbody
      exact ⟨.cfg R ht hb, .cfg R eq (fun i => .paper (.refl (hb i)))⟩
    | _ => simp [Site.rewriteAt] at hm
  | block i next ih =>
    cases hr with
    | cfg R he hb =>
      simp only [Site.rewriteAt] at hm
      split at hm
      next hi =>
        obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hm
        obtain ⟨ht, eq⟩ := ih (hb ⟨i, hi⟩) hbody
        refine ⟨.cfg R he ?_, .cfg R (.paper (.refl he)) ?_⟩
        · intro j
          by_cases h : j = ⟨i, hi⟩
          · subst j
            simpa using ht
          · simpa [Function.update_apply, h] using hb j
        · intro j
          by_cases h : j = ⟨i, hi⟩
          · subst j
            simpa using eq
          · simpa [Function.update_apply, h] using
              (Paper.Extension.Eqv.paper (Seed := Seed) (.refl (hb j)))
      next _ => contradiction
    | _ => simp [Site.rewriteAt] at hm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetTraversal
