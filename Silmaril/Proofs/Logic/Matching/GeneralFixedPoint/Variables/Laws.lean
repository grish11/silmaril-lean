module

public import Silmaril.Proofs.Logic.Matching.GeneralFixedPoint.Variables.Substitution

@[expose] public section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open Algebraic.ManySorted (Signature)
open FixedPoint (Ren)
variable {S : Type}

private theorem lift_identity {k : Nat} (Γ : Fin k → S) (s : S) :
    Ren.lift (Γ := Γ) (Δ := Γ) (fun i => ⟨i, rfl⟩) s = (fun i => ⟨i, rfl⟩) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem renameFirstOrder_id {A : Signature S} {k : Nat} {Γ : Fin k → S} {s : S}
    (p : FirstOrder.Pattern A Γ s) :
    FixedPoint.renameFirstOrder p (fun i => ⟨i, rfl⟩) = p := by
  induction p with
  | var => rfl
  | app op args ih => exact congrArg (FirstOrder.Pattern.app op) (funext ih)
  | neg p hp => exact congrArg FirstOrder.Pattern.neg hp
  | conj p q hp hq => exact congrArg₂ FirstOrder.Pattern.conj hp hq
  | ex bound p hp =>
      change FirstOrder.Pattern.ex bound
        (FixedPoint.renameFirstOrder p (Ren.lift (fun i => ⟨i, rfl⟩) bound)) = _
      exact congrArg (FirstOrder.Pattern.ex bound)
        ((congrArg (fun ρ => FixedPoint.renameFirstOrder p ρ) (lift_identity _ bound)).trans hp)


theorem Pattern.renameObjects_id {A : Signature S} {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    p.renameObjects (fun i => ⟨i, rfl⟩) = p := by
  induction p with
  | base p => exact congrArg Pattern.base (renameFirstOrder_id p)
  | setvar => rfl
  | app op args ih => exact congrArg (Pattern.app op) (funext ih)
  | neg p hp => exact congrArg Pattern.neg hp
  | conj p q hp hq => exact congrArg₂ Pattern.conj hp hq
  | ex bound p hp =>
      change Pattern.ex bound (p.renameObjects (Ren.lift (fun i => ⟨i, rfl⟩) bound)) = _
      exact congrArg (Pattern.ex bound)
        ((congrArg (fun ρ => p.renameObjects ρ) (lift_identity _ bound)).trans hp)
  | mu p hp => exact congrArg Pattern.mu hp
  | nu p hp => exact congrArg Pattern.nu hp

private theorem context_cases {r : Nat} (P : Fin (r+1) → S) :
    ∃ t T, P = Fin.cases t T :=
  ⟨P 0, P ∘ Fin.succ, funext (fun i => Fin.cases rfl (fun _ => rfl) i)⟩

theorem Pattern.renameSets_id {A : Signature S} {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    p.renameSets (fun i => ⟨i, rfl⟩) = p := by
  induction p with
  | base => rfl
  | setvar => rfl
  | app op args ih => exact congrArg (Pattern.app op) (funext ih)
  | neg p hp => exact congrArg Pattern.neg hp
  | conj p q hp hq => exact congrArg₂ Pattern.conj hp hq
  | ex bound p hp => exact congrArg (Pattern.ex bound) hp
  | @mu r k P' Γ p hp =>
      obtain ⟨t, T, h⟩ := context_cases P'
      subst P'
      change Pattern.mu (p.renameSets (Ren.liftHead (fun i => ⟨i, rfl⟩))) = _
      have he : Ren.liftHead (P' := Fin.cases t T) (fun i => ⟨i, rfl⟩) =
          (fun i => ⟨i, rfl⟩) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      exact congrArg Pattern.mu ((congrArg (fun ρ => p.renameSets ρ) he).trans hp)
  | @nu r k P' Γ p hp =>
      obtain ⟨t, T, h⟩ := context_cases P'
      subst P'
      change Pattern.nu (p.renameSets (Ren.liftHead (fun i => ⟨i, rfl⟩))) = _
      have he : Ren.liftHead (P' := Fin.cases t T) (fun i => ⟨i, rfl⟩) =
          (fun i => ⟨i, rfl⟩) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      exact congrArg Pattern.nu ((congrArg (fun ρ => p.renameSets ρ) he).trans hp)

/-- Substitution identity is semantic: expanding a compressed first-order leaf
need not reproduce its original syntax. -/
theorem Pattern.denote_substitute_id {A : Signature S} (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s)
    (v : ObjEnv A M Γ) (η : SetEnv A M P) :
    (p.substitute (fun i => .setvar i) (fun i => .base (.var i))).denote M v η =
      p.denote M v η :=
  p.denote_substitute_env M _ _ v η v η (fun _ => rfl) (fun _ => rfl)

/-- Semantic fusion of simultaneous substitutions, with the necessary singleton
conditions on the two element substitutions. -/
theorem Pattern.denote_substitute_comp {A : Signature S} (M : Model A) {r k a b c d : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {Q : Fin a → S} {Δ : Fin b → S}
    {R : Fin c → S} {Ε : Fin d → S} {s : S}
    (p : Pattern A P Γ s) (σ : ∀ i, Pattern A Q Δ (P i))
    (τ : ∀ i, Pattern A Q Δ (Γ i))
    (υ : ∀ i, Pattern A R Ε (Q i)) (χ : ∀ i, Pattern A R Ε (Δ i))
    (v : ObjEnv A M Ε) (η : SetEnv A M R) (w : ObjEnv A M Δ) (u : ObjEnv A M Γ)
    (hχ : ∀ i, (χ i).denote M v η = {w i})
    (hτ : ∀ i, (τ i).denote M w (fun j => (υ j).denote M v η) = {u i}) :
    ((p.substitute σ τ).substitute υ χ).denote M v η =
      (p.substitute (fun i => (σ i).substitute υ χ)
        (fun i => (τ i).substitute υ χ)).denote M v η := by
  rw [Pattern.denote_substitute M _ υ χ v η w hχ,
    Pattern.denote_substitute M p σ τ w _ u hτ]
  symm
  apply p.denote_substitute_env M _ _ v η u _
  · intro i
    exact (σ i).denote_substitute M υ χ v η w hχ
  · intro i
    exact ((τ i).denote_substitute M υ χ v η w hχ).trans (hτ i)

end Silmaril.Logic.Matching.GeneralFixedPoint
