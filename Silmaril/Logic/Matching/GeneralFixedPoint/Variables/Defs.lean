module

public import Silmaril.Logic.Matching.GeneralFixedPoint.Thms
public import Silmaril.Logic.Matching.FixedPoint.Variables.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open Algebraic.ManySorted (Signature)
open FixedPoint (Ren)
variable {S : Type}

/-- Composition of sorted renamings, in source-to-target order. -/
def composeRen {k l m : Nat} {Γ : Fin k → S} {Δ : Fin l → S} {Ε : Fin m → S}
    (ρ : Ren Γ Δ) (υ : Ren Δ Ε) : Ren Γ Ε :=
  fun i => ⟨(υ (ρ i).val).val, (υ (ρ i).val).property.trans (ρ i).property⟩

def Pattern.renameObjects {A : Signature S} {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    {l : Nat} → {Δ : Fin l → S} → Ren Γ Δ → Pattern A P Δ s := by
  induction p with
  | base p => intro l Δ ρ; exact .base (FixedPoint.renameFirstOrder p ρ)
  | setvar i => intro l Δ ρ; exact .setvar i
  | app op args ih => intro l Δ ρ; exact .app op (fun i => ih i ρ)
  | neg p hp => intro l Δ ρ; exact .neg (hp ρ)
  | conj p q hp hq => intro l Δ ρ; exact .conj (hp ρ) (hq ρ)
  | ex bound p hp => intro l Δ ρ; exact .ex bound (hp (FixedPoint.Ren.lift ρ bound))
  | mu p hp => intro l Δ ρ; exact .mu (hp ρ)
  | nu p hp => intro l Δ ρ; exact .nu (hp ρ)

def Pattern.renameSets {A : Signature S} {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    {l : Nat} → {Q : Fin l → S} → Ren P Q → Pattern A Q Γ s := by
  induction p with
  | base p => intro l Q ρ; exact .base p
  | setvar i => intro l Q ρ; exact (ρ i).property ▸ Pattern.setvar (ρ i).val
  | app op args ih => intro l Q ρ; exact .app op (fun i => ih i ρ)
  | neg p hp => intro l Q ρ; exact .neg (hp ρ)
  | conj p q hp hq => intro l Q ρ; exact .conj (hp ρ) (hq ρ)
  | ex bound p hp => intro l Q ρ; exact .ex bound (hp ρ)
  | @mu r k P' Γ p hp =>
      intro l Q ρ
      exact Pattern.mu (P' := Fin.cases (P' 0) Q) (hp (FixedPoint.Ren.liftHead ρ))
  | @nu r k P' Γ p hp =>
      intro l Q ρ
      exact Pattern.nu (P' := Fin.cases (P' 0) Q) (hp (FixedPoint.Ren.liftHead ρ))

/-- Expand a first-order leaf while simultaneously replacing its element variables.
An element binder preserves its fresh variable and shifts every old replacement. -/
def substituteFirstOrder {A : Signature S} {k : Nat} {Γ : Fin k → S} {s : S}
    (p : FirstOrder.Pattern A Γ s) :
    {r l : Nat} → {Q : Fin r → S} → {Δ : Fin l → S} →
      (∀ i, Pattern A Q Δ (Γ i)) → Pattern A Q Δ s := by
  induction p with
  | var i => intro r l Q Δ τ; exact τ i
  | app op args ih => intro r l Q Δ τ; exact .app op (fun i => ih i τ)
  | neg p hp => intro r l Q Δ τ; exact .neg (hp τ)
  | conj p q hp hq => intro r l Q Δ τ; exact .conj (hp τ) (hq τ)
  | ex bound p hp =>
      intro r l Q Δ τ
      exact .ex bound (hp (Fin.cases (.base (.var 0))
        (fun i => (τ i).renameObjects (FixedPoint.Ren.shift Δ bound))))

/-- Simultaneous substitution of both variable namespaces. Replacements may
contain either namespace. Both are shifted under each relevant binder, so free
variables in replacements cannot be captured. -/
def Pattern.substitute {A : Signature S} {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    {a b : Nat} → {Q : Fin a → S} → {Δ : Fin b → S} →
      (∀ i, Pattern A Q Δ (P i)) →
      (∀ i, Pattern A Q Δ (Γ i)) → Pattern A Q Δ s := by
  induction p with
  | base p => intro a b Q Δ σ τ; exact substituteFirstOrder p τ
  | setvar i => intro a b Q Δ σ τ; exact σ i
  | app op args ih => intro a b Q Δ σ τ; exact .app op (fun i => ih i σ τ)
  | neg p hp => intro a b Q Δ σ τ; exact .neg (hp σ τ)
  | conj p q hp hq => intro a b Q Δ σ τ; exact .conj (hp σ τ) (hq σ τ)
  | ex bound p hp =>
      intro a b Q Δ σ τ
      exact .ex bound (hp
        (fun i => (σ i).renameObjects (FixedPoint.Ren.shift Δ bound))
        (Fin.cases (.base (.var 0))
          (fun i => (τ i).renameObjects (FixedPoint.Ren.shift Δ bound))))
  | @mu r k P' Γ p hp =>
      intro a b Q Δ σ τ
      exact Pattern.mu (P' := Fin.cases (P' 0) Q) (hp
        (Fin.cases (.setvar 0)
          (fun i => (σ i).renameSets (FixedPoint.Ren.shift Q (P' 0))))
        (fun i => (τ i).renameSets (FixedPoint.Ren.shift Q (P' 0))))
  | @nu r k P' Γ p hp =>
      intro a b Q Δ σ τ
      exact Pattern.nu (P' := Fin.cases (P' 0) Q) (hp
        (Fin.cases (.setvar 0)
          (fun i => (σ i).renameSets (FixedPoint.Ren.shift Q (P' 0))))
        (fun i => (τ i).renameSets (FixedPoint.Ren.shift Q (P' 0))))

/-- Substitute arbitrary set patterns, keeping element variables unchanged. -/
def Pattern.substituteSets {A : Signature S} {r k a : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {Q : Fin a → S} {s : S} (p : Pattern A P Γ s)
    (σ : ∀ i, Pattern A Q Γ (P i)) : Pattern A Q Γ s :=
  p.substitute σ (fun i => .base (.var i))

/-- Substitute element patterns, keeping set variables unchanged. Semantic
substitution requires singleton denotations of these replacements. -/
def Pattern.substituteObjects {A : Signature S} {r k b : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {Δ : Fin b → S} {s : S} (p : Pattern A P Γ s)
    (τ : ∀ i, Pattern A P Δ (Γ i)) : Pattern A P Δ s :=
  p.substitute (fun i => .setvar i) τ

end Silmaril.Logic.Matching.GeneralFixedPoint
