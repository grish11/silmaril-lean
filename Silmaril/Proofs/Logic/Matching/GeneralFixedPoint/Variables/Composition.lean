module

public import Silmaril.Logic.Matching.GeneralFixedPoint.Variables.Defs

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open Algebraic.ManySorted (Signature)
open FixedPoint (Ren)
variable {S : Type}

private theorem cast_trans (F : S → Type) {a b c : S} (h : a = b) (k : b = c) (x : F a) :
    k ▸ (h ▸ x) = (h.trans k) ▸ x := by
  cases h
  cases k
  rfl

private theorem lift_comp {k l m : Nat} {Γ : Fin k → S} {Δ : Fin l → S} {Ε : Fin m → S}
    (ρ : Ren Γ Δ) (υ : Ren Δ Ε) (s : S) :
    composeRen (ρ.lift s) (υ.lift s) = (composeRen ρ υ).lift s := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem liftHead_comp {k l m : Nat} {P : Fin (k+1) → S}
    {Q : Fin l → S} {R : Fin m → S} (ρ : Ren (P ∘ Fin.succ) Q) (υ : Ren Q R) :
    composeRen (Ren.liftHead ρ) (υ.lift (P 0)) = Ren.liftHead (composeRen ρ υ) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem firstOrder_cast_rename {A : Signature S} {k l : Nat}
    {Γ : Fin k → S} {Δ : Fin l → S} {s t : S} (h : s = t)
    (p : FirstOrder.Pattern A Γ s) (ρ : Ren Γ Δ) :
    FixedPoint.renameFirstOrder (h ▸ p) ρ = h ▸ FixedPoint.renameFirstOrder p ρ := by
  cases h
  rfl

private theorem sets_cast_rename {A : Signature S} {r k a : Nat}
    {P : Fin r → S} {Q : Fin a → S} {Γ : Fin k → S} {s t : S} (h : s = t)
    (p : Pattern A P Γ s) (ρ : Ren P Q) :
    (h ▸ p).renameSets ρ = h ▸ p.renameSets ρ := by
  cases h
  rfl

theorem renameFirstOrder_comp {A : Signature S} {k : Nat} {Γ : Fin k → S} {s : S}
    (p : FirstOrder.Pattern A Γ s) :
    ∀ {l m : Nat} {Δ : Fin l → S} {Ε : Fin m → S} (ρ : Ren Γ Δ) (υ : Ren Δ Ε),
      FixedPoint.renameFirstOrder (FixedPoint.renameFirstOrder p ρ) υ =
        FixedPoint.renameFirstOrder p (composeRen ρ υ) := by
  induction p with
  | @var k Γ i =>
      intro l m Δ Ε ρ υ
      change FixedPoint.renameFirstOrder ((ρ i).property ▸ FirstOrder.Pattern.var (A := A) (Γ := Δ) (ρ i).val) υ = _
      rw [firstOrder_cast_rename]
      exact cast_trans (FirstOrder.Pattern A Ε) (υ (ρ i).val).property (ρ i).property _
  | app op args ih =>
      intros
      exact congrArg (FirstOrder.Pattern.app op) (funext (fun i => ih i _ _))
  | neg p hp => intros; exact congrArg FirstOrder.Pattern.neg (hp _ _)
  | conj p q hp hq => intros; exact congrArg₂ FirstOrder.Pattern.conj (hp _ _) (hq _ _)
  | ex bound p hp =>
      intro l m Δ Ε ρ υ
      change FirstOrder.Pattern.ex bound
        (FixedPoint.renameFirstOrder (FixedPoint.renameFirstOrder p (ρ.lift bound)) (υ.lift bound)) = _
      rw [hp, lift_comp]
      rfl

theorem Pattern.renameObjects_comp {A : Signature S} {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {l m : Nat} {Δ : Fin l → S} {Ε : Fin m → S} (ρ : Ren Γ Δ) (υ : Ren Δ Ε),
      (p.renameObjects ρ).renameObjects υ = p.renameObjects (composeRen ρ υ) := by
  induction p with
  | base p => intros; exact congrArg Pattern.base (renameFirstOrder_comp p _ _)
  | setvar => intros; rfl
  | app op args ih => intros; exact congrArg (Pattern.app op) (funext (fun i => ih i _ _))
  | neg p hp => intros; exact congrArg Pattern.neg (hp _ _)
  | conj p q hp hq => intros; exact congrArg₂ Pattern.conj (hp _ _) (hq _ _)
  | ex bound p hp =>
      intro l m Δ Ε ρ υ
      change Pattern.ex bound ((p.renameObjects (ρ.lift bound)).renameObjects (υ.lift bound)) = _
      rw [hp, lift_comp]
      rfl
  | mu p hp => intros; exact congrArg Pattern.mu (hp _ _)
  | nu p hp => intros; exact congrArg Pattern.nu (hp _ _)

theorem Pattern.renameSets_comp {A : Signature S} {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {a b : Nat} {Q : Fin a → S} {R : Fin b → S} (ρ : Ren P Q) (υ : Ren Q R),
      (p.renameSets ρ).renameSets υ = p.renameSets (composeRen ρ υ) := by
  induction p with
  | base => intros; rfl
  | @setvar r k P Γ i =>
      intro a b Q R ρ υ
      change (((ρ i).property ▸ (Pattern.setvar (A := A) (P := Q) (Γ := Γ) (ρ i).val)).renameSets υ) = _
      rw [sets_cast_rename]
      exact cast_trans (Pattern A R _) (υ (ρ i).val).property (ρ i).property _
  | app op args ih => intros; exact congrArg (Pattern.app op) (funext (fun i => ih i _ _))
  | neg p hp => intros; exact congrArg Pattern.neg (hp _ _)
  | conj p q hp hq => intros; exact congrArg₂ Pattern.conj (hp _ _) (hq _ _)
  | ex bound p hp => intros; exact congrArg (Pattern.ex bound) (hp _ _)
  | @mu r k P' Γ p hp =>
      intro a b Q R ρ υ
      change Pattern.mu (P' := Fin.cases (P' 0) R) ((p.renameSets (Ren.liftHead ρ)).renameSets (υ.lift (P' 0))) = _
      rw [hp, liftHead_comp]
      rfl
  | @nu r k P' Γ p hp =>
      intro a b Q R ρ υ
      change Pattern.nu (P' := Fin.cases (P' 0) R) ((p.renameSets (Ren.liftHead ρ)).renameSets (υ.lift (P' 0))) = _
      rw [hp, liftHead_comp]
      rfl

end Silmaril.Logic.Matching.GeneralFixedPoint
