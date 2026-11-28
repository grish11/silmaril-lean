module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Factorization.Defs
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycleFactorization

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.Extension.Singleton
open Paper.Extension.Singleton.ThreeCycle
open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

local notation "Q" => TypeCategory Seed

theorem partialFold_comp_fold (A : Q) (keep : Fin 3) :
    partialFold A keep ≫ coprod.desc (𝟙 A) (𝟙 A) = fold A := by
  fin_cases keep <;>
    (apply coprod.hom_ext
     · simp [partialFold]
     · apply coprod.hom_ext <;> simp [partialFold])

theorem collapse_of_shared_phases {A B X D : Q}
    (g : A ⟶ B ⨿ A) (x : X ⟶ A) (repeats : x ≫ g = x ≫ coprod.inr)
    (h : A ⨿ (A ⨿ A) ⟶ D) (exit : B ⟶ D) (next : D ⟶ B ⨿ D)
    (square : step g ≫ coprod.map (𝟙 B) h = h ≫ next) :
    let first := x ≫ coprod.inl ≫ h
    let second := x ≫ (coprod.inl ≫ coprod.inr) ≫ h
    let third := x ≫ (coprod.inr ≫ coprod.inr) ≫ h
    (first = second ∨ second = third ∨ third = first) → first = second ∧ second = third := by
  let i₀ : A ⟶ A ⨿ (A ⨿ A) := coprod.inl
  let i₁ : A ⟶ A ⨿ (A ⨿ A) := coprod.inl ≫ coprod.inr
  let i₂ : A ⟶ A ⨿ (A ⨿ A) := coprod.inr ≫ coprod.inr
  let a := x ≫ i₀ ≫ h
  let b := x ≫ i₁ ≫ h
  let c := x ≫ i₂ ≫ h
  have advance {i j : A ⟶ A ⨿ (A ⨿ A)} (row : i ≫ step g = g ≫ coprod.map (𝟙 B) j) :
      (x ≫ i ≫ h) ≫ next = (x ≫ j ≫ h) ≫ coprod.inr := by
    simp only [Category.assoc]
    rw [← square, ← Category.assoc i (step g), row]
    simp only [Category.assoc, ← Category.assoc x g, repeats, coprod.inr_map_assoc, coprod.inr_map]
  have ha : a ≫ next = b ≫ coprod.inr := advance (by simp [i₀, i₁, step])
  have hb : b ≫ next = c ≫ coprod.inr := advance (by simp [i₁, i₂, step])
  have hc : c ≫ next = a ≫ coprod.inr := advance (by simp [i₂, i₀, step])
  have propagate {p q p' q' : X ⟶ D} (hp : p ≫ next = p' ≫ coprod.inr)
      (hq : q ≫ next = q' ≫ coprod.inr) (same : p = q) : p' = q' := by
    have eq := hp.symm.trans ((congrArg (· ≫ next) same).trans hq)
    simpa using congrArg (· ≫ coprod.desc exit (𝟙 D)) eq
  change (a = b ∨ b = c ∨ c = a) → a = b ∧ b = c
  rintro (ab | bc | ca)
  · exact ⟨ab, propagate ha hb ab⟩
  · exact ⟨propagate hc ha (propagate hb hc bc), bc⟩
  · have ab := propagate hc ha ca
    exact ⟨ab, propagate ha hb ab⟩

theorem no_partial_fold_square {X A B : Q} (g : A ⟶ B ⨿ A)
    (x : X ⟶ A) (repeats : x ≫ g = x ≫ coprod.inr)
    (distinct : x ≫ (coprod.inl : A ⟶ A ⨿ A) ≠ x ≫ coprod.inr)
    (exit : B ⟶ A ⨿ A) (keep : Fin 3) (next : A ⨿ A ⟶ B ⨿ (A ⨿ A)) :
    step g ≫ coprod.map (𝟙 B) (partialFold A keep) ≠ partialFold A keep ≫ next := by
  intro square
  have collapse := collapse_of_shared_phases g x repeats (partialFold A keep) exit next square
  fin_cases keep
  · simp [Category.assoc, partialFold] at collapse
    exact distinct collapse
  · simp [Category.assoc, partialFold] at collapse
    exact distinct collapse.1.symm
  · simp [Category.assoc, partialFold] at collapse
    exact distinct collapse.symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycleFactorization
