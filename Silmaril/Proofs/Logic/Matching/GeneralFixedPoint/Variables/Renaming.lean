module

public import Silmaril.Logic.Matching.GeneralFixedPoint.Variables.Defs

@[expose] public section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open Algebraic.ManySorted (Signature)
open FixedPoint (Ren)
variable {S : Type}

theorem Pattern.denote_renameObjects {A : Signature S} (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {l : Nat} {Δ : Fin l → S} (ρ : Ren Γ Δ) (v : ObjEnv A M Δ) (η : SetEnv A M P),
      (p.renameObjects ρ).denote M v η = p.denote M (Ren.pull M.carrier v ρ) η := by
  induction p with
  | base p =>
      intro l Δ ρ v η
      exact FixedPoint.renameFirstOrder_denote M p ρ v
  | setvar => intro l Δ ρ v η; rfl
  | app op args ih =>
      intro l Δ ρ v η
      change FixedPoint.application M op (fun i => (renameObjects (args i) ρ).denote M v η) = _
      simp only [ih]
      rfl
  | neg p hp =>
      intro l Δ ρ v η
      exact congrArg (fun X => Xᶜ) (hp ρ v η)
  | conj p q hp hq =>
      intro l Δ ρ v η
      change (p.renameObjects ρ).denote M v η ∩ (q.renameObjects ρ).denote M v η = _
      rw [hp, hq]
      rfl
  | ex bound p hp =>
      intro l Δ ρ v η
      change {x | ∃ a : M.carrier bound, x ∈ (p.renameObjects (ρ.lift bound)).denote M (Fin.cases a v) η} = _
      simp only [hp, Ren.pull_lift]
      rfl
  | mu p hp =>
      intro l Δ ρ v η
      change sInf {X | (p.renameObjects ρ).denote M v (Fin.cases X η) ⊆ X} = _
      simp only [hp]
      rfl
  | nu p hp =>
      intro l Δ ρ v η
      change sSup {X | X ⊆ (p.renameObjects ρ).denote M v (Fin.cases X η)} = _
      simp only [hp]
      rfl

theorem denote_setvar_cast {A : Signature S} (M : Model A) {r k : Nat}
    {Q : Fin r → S} {Γ : Fin k → S} (v : ObjEnv A M Γ) (η : SetEnv A M Q)
    {t : S} (j : Fin r) (h : Q j = t) :
    (h ▸ Pattern.setvar (A := A) (Γ := Γ) (P := Q) j).denote M v η = h ▸ η j := by
  cases h
  rfl

theorem Pattern.denote_renameSets {A : Signature S} (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {l : Nat} {Q : Fin l → S} (ρ : Ren P Q) (v : ObjEnv A M Γ) (η : SetEnv A M Q),
      (p.renameSets ρ).denote M v η = p.denote M v (Ren.pull (fun s => Set (M.carrier s)) η ρ) := by
  induction p with
  | base => intro l Q ρ v η; rfl
  | setvar i => intro l Q ρ v η; exact denote_setvar_cast M v η (ρ i).val (ρ i).property
  | app op args ih =>
      intro l Q ρ v η
      change FixedPoint.application M op (fun i => (renameSets (args i) ρ).denote M v η) = _
      simp only [ih]
      rfl
  | neg p hp =>
      intro l Q ρ v η
      exact congrArg (fun X => Xᶜ) (hp ρ v η)
  | conj p q hp hq =>
      intro l Q ρ v η
      exact congrArg₂ Set.inter (hp ρ v η) (hq ρ v η)
  | ex bound p hp =>
      intro l Q ρ v η
      change {x | ∃ a : M.carrier bound, x ∈ (p.renameSets ρ).denote M (Fin.cases a v) η} = _
      simp only [hp]
      rfl
  | @mu r k P' Γ p hp =>
      intro l Q ρ v η
      change sInf {X | (p.renameSets (Ren.liftHead ρ)).denote M v (Fin.cases X η) ⊆ X} = _
      simp only [hp, Ren.pull_liftHead]
      rfl
  | @nu r k P' Γ p hp =>
      intro l Q ρ v η
      change sSup {X | X ⊆ (p.renameSets (Ren.liftHead ρ)).denote M v (Fin.cases X η)} = _
      simp only [hp, Ren.pull_liftHead]
      rfl

end Silmaril.Logic.Matching.GeneralFixedPoint
