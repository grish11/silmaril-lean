module

public import Silmaril.Logic.Matching.GeneralFixedPoint.SetObjects.Defs

@[expose] public section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open Algebraic.ManySorted (Signature)
open FixedPoint (Ren)
variable {S : Type}

private theorem firstOrderSets_var_cast {A : Signature S} (M : Model A)
    {k : Nat} {Γ : Fin k → S} (v : SetObjEnv M Γ) {s : S} (i : Fin k) (h : Γ i = s) :
    denoteFirstOrderSets M (h ▸ FirstOrder.Pattern.var i) v = h ▸ v i := by
  cases h
  rfl

theorem renameFirstOrderSets_denote {A : Signature S} (M : Model A) {k : Nat}
    {Γ : Fin k → S} {s : S} (p : FirstOrder.Pattern A Γ s) :
    ∀ {l : Nat} {Δ : Fin l → S} (ρ : Ren Γ Δ) (v : SetObjEnv M Δ),
      denoteFirstOrderSets M (FixedPoint.renameFirstOrder p ρ) v =
        denoteFirstOrderSets M p (Ren.pull (fun s => Set (M.carrier s)) v ρ) := by
  induction p with
  | var i => intro l Δ ρ v; exact firstOrderSets_var_cast M v (ρ i).val (ρ i).property
  | app op args ih =>
      intro l Δ ρ v
      change FixedPoint.application M op
        (fun i => denoteFirstOrderSets M (FixedPoint.renameFirstOrder (args i) ρ) v) = _
      simp only [ih]
      rfl
  | neg p hp => intro l Δ ρ v; exact congrArg (fun X => Xᶜ) (hp ρ v)
  | conj p q hp hq => intro l Δ ρ v; exact congrArg₂ Set.inter (hp ρ v) (hq ρ v)
  | ex bound p hp =>
      intro l Δ ρ v
      change {x | ∃ a : M.carrier bound, x ∈
        denoteFirstOrderSets M (FixedPoint.renameFirstOrder p (ρ.lift bound)) (Fin.cases {a} v)} = _
      have pull (a : M.carrier bound) :
          Ren.pull (fun s => Set (M.carrier s)) (Fin.cases {a} v) (ρ.lift bound) =
            Fin.cases {a} (Ren.pull (fun s => Set (M.carrier s)) v ρ) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      simp only [hp, pull]
      rfl

theorem Pattern.denoteSetObjects_renameObjects {A : Signature S} (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {l : Nat} {Δ : Fin l → S} (ρ : Ren Γ Δ) (v : SetObjEnv M Δ) (η : SetEnv A M P),
      (p.renameObjects ρ).denoteSetObjects M v η = p.denoteSetObjects M (Ren.pull (fun s => Set (M.carrier s)) v ρ) η := by
  induction p with
  | base p =>
      intro l Δ ρ v η
      exact renameFirstOrderSets_denote M p ρ v
  | setvar => intro l Δ ρ v η; rfl
  | app op args ih =>
      intro l Δ ρ v η
      change FixedPoint.application M op (fun i => (renameObjects (args i) ρ).denoteSetObjects M v η) = _
      simp only [ih]
      rfl
  | neg p hp =>
      intro l Δ ρ v η
      exact congrArg (fun X => Xᶜ) (hp ρ v η)
  | conj p q hp hq =>
      intro l Δ ρ v η
      change (p.renameObjects ρ).denoteSetObjects M v η ∩ (q.renameObjects ρ).denoteSetObjects M v η = _
      rw [hp, hq]
      rfl
  | ex bound p hp =>
      intro l Δ ρ v η
      change {x | ∃ a : M.carrier bound, x ∈ (p.renameObjects (ρ.lift bound)).denoteSetObjects M (Fin.cases {a} v) η} = _
      have pull (a : M.carrier bound) :
          Ren.pull (fun s => Set (M.carrier s)) (Fin.cases {a} v) (ρ.lift bound) =
            Fin.cases {a} (Ren.pull (fun s => Set (M.carrier s)) v ρ) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      simp only [hp, pull]
      rfl
  | mu p hp =>
      intro l Δ ρ v η
      change sInf {X | (p.renameObjects ρ).denoteSetObjects M v (Fin.cases X η) ⊆ X} = _
      simp only [hp]
      rfl
  | nu p hp =>
      intro l Δ ρ v η
      change sSup {X | X ⊆ (p.renameObjects ρ).denoteSetObjects M v (Fin.cases X η)} = _
      simp only [hp]
      rfl

theorem denoteSetObjects_setvar_cast {A : Signature S} (M : Model A) {r k : Nat}
    {Q : Fin r → S} {Γ : Fin k → S} (v : SetObjEnv M Γ) (η : SetEnv A M Q)
    {t : S} (j : Fin r) (h : Q j = t) :
    (h ▸ Pattern.setvar (A := A) (Γ := Γ) (P := Q) j).denoteSetObjects M v η = h ▸ η j := by
  cases h
  rfl

theorem Pattern.denoteSetObjects_renameSets {A : Signature S} (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {l : Nat} {Q : Fin l → S} (ρ : Ren P Q) (v : SetObjEnv M Γ) (η : SetEnv A M Q),
      (p.renameSets ρ).denoteSetObjects M v η = p.denoteSetObjects M v (Ren.pull (fun s => Set (M.carrier s)) η ρ) := by
  induction p with
  | base => intro l Q ρ v η; rfl
  | setvar i => intro l Q ρ v η; exact denoteSetObjects_setvar_cast M v η (ρ i).val (ρ i).property
  | app op args ih =>
      intro l Q ρ v η
      change FixedPoint.application M op (fun i => (renameSets (args i) ρ).denoteSetObjects M v η) = _
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
      change {x | ∃ a : M.carrier bound, x ∈ (p.renameSets ρ).denoteSetObjects M (Fin.cases {a} v) η} = _
      simp only [hp]
      rfl
  | @mu r k P' Γ p hp =>
      intro l Q ρ v η
      change sInf {X | (p.renameSets (Ren.liftHead ρ)).denoteSetObjects M v (Fin.cases X η) ⊆ X} = _
      simp only [hp, Ren.pull_liftHead]
      rfl
  | @nu r k P' Γ p hp =>
      intro l Q ρ v η
      change sSup {X | X ⊆ (p.renameSets (Ren.liftHead ρ)).denoteSetObjects M v (Fin.cases X η)} = _
      simp only [hp, Ren.pull_liftHead]
      rfl

end Silmaril.Logic.Matching.GeneralFixedPoint
