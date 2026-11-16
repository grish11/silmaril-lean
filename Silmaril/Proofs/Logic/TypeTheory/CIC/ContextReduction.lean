module

public import Silmaril.Logic.TypeTheory.CIC.Reduction.Thms
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.ContextReductionLaws

open Silmaril.Logic.TypeTheory.CIC

theorem assumptionCount_eq_length {Γ : Context} (hnone : ∀ d ∈ Γ, d.value = none) :
    Γ.assumptionCount = Γ.length := by
  induction Γ with
  | nil => rfl
  | cons d Γ ih =>
      have hd := hnone d (by simp)
      have ht := ih (fun e he => hnone e (by simp only [List.mem_cons]; exact Or.inr he))
      simp [Context.assumptionCount, hd, ht, Nat.add_comm]

private theorem noDefinitions_mapIdx {Γ : Context} (hnone : ∀ d ∈ Γ, d.value = none)
    (f : ℕ → Expr → Expr) : ∀ d ∈ Γ.mapIdx (fun i d => d.mapTerms (f i)), d.value = none := by
  induction Γ generalizing f with
  | nil => simp
  | cons d Γ ih =>
      have hd := hnone d (by simp)
      have ht := ih (fun e he => hnone e (by simp only [List.mem_cons]; exact Or.inr he)) (fun i => f (i + 1))
      intro e he
      simp only [List.mapIdx_cons, List.mem_cons] at he
      rcases he with rfl | he
      · simp only [ContextDecl.mapTerms, hd, Option.map_none]
      · exact ht e he

theorem instantiateCase_noDefinitions {Γ : Context} (hnone : ∀ d ∈ Γ, d.value = none)
    (p : Predicate Expr LevelName) : ∀ d ∈ Context.instantiateCase p Γ, d.value = none := by
  have hi : ∀ d ∈ Context.instantiate p.universeInstance Γ, d.value = none := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    simp only [ContextDecl.mapTerms, hnone e he, Option.map_none]
  exact noDefinitions_mapIdx hi _


/-- Two no-definition declaration caches of equal length have the same actual replacement indices. -/
theorem extendedSubst_eq_of_noDefinitions {Γ Δ : Context}
    (hΓ : ∀ d ∈ Γ, d.value = none) (hΔ : ∀ d ∈ Δ, d.value = none) (hlen : Γ.length = Δ.length) (offset : ℕ) :
    Γ.extendedSubst offset = Δ.extendedSubst offset := by
  induction Γ generalizing Δ offset with
  | nil =>
      have hnil : Δ = [] := by simpa using hlen.symm
      subst Δ
      rfl
  | cons d Γ ih =>
      cases Δ with
      | nil => simp at hlen
      | cons e Δ =>
          have hd := hΓ d (by simp)
          have he := hΔ e (by simp)
          have ht := ih (fun x hx => hΓ x (by simp only [List.mem_cons]; exact Or.inr hx))
            (fun x hx => hΔ x (by simp only [List.mem_cons]; exact Or.inr hx)) (by simpa using hlen) (offset + 1)
          simp only [Context.extendedSubst, hd, he, ht]

/-- No-definition replacement indices contain no universe-sensitive syntax. -/
theorem extendedSubst_substUniverses (σ : LevelName → Universe) {Γ : Context}
    (hΓ : ∀ d ∈ Γ, d.value = none) (offset : ℕ) :
    (Γ.extendedSubst offset).map (Term.substUniverses σ) = Γ.extendedSubst offset := by
  induction Γ generalizing offset with
  | nil => rfl
  | cons d Γ ih =>
      have hd := hΓ d (by simp)
      have ht := ih (fun x hx => hΓ x (by simp only [List.mem_cons]; exact Or.inr hx)) (offset + 1)
      simp only [Context.extendedSubst, hd, List.map_cons, Term.substUniverses, ht]

/-- Definition-free cache expansion depends on its length, not declaration types or names. -/
theorem expandLets_eq_of_noDefinitions {Γ Δ : Context}
    (hΓ : ∀ d ∈ Γ, d.value = none) (hΔ : ∀ d ∈ Δ, d.value = none) (hlen : Γ.length = Δ.length) (body : Expr) :
    Γ.expandLets body = Δ.expandLets body := by
  simp only [Context.expandLets, assumptionCount_eq_length hΓ, assumptionCount_eq_length hΔ,
    hlen, extendedSubst_eq_of_noDefinitions hΓ hΔ hlen]

end Silmaril.Proofs.Logic.TypeTheory.CIC.ContextReductionLaws
