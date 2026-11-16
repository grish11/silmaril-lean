module

public import Silmaril.Logic.Matching.FixedPoint.Defs

@[expose] public section
namespace Silmaril.Logic.Matching.FixedPoint
open CategoryTheory
open Algebraic.ManySorted (Signature)
variable {S : Type} {A B C : Signature S}

theorem Pattern.map_id {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S}
    (p : Pattern A P Γ s) : p.map (𝟙 A) = p := by
  induction p with
  | base p => exact congrArg Pattern.base (FirstOrder.Pattern.map_id p)
  | setvar => rfl
  | app op args ih => exact congrArg (Pattern.app op) (funext ih)
  | dualApp op args ih => exact congrArg (Pattern.dualApp op) (funext ih)
  | conj p q hp hq => exact congrArg₂ Pattern.conj hp hq
  | disj p q hp hq => exact congrArg₂ Pattern.disj hp hq
  | ex bound p hp => exact congrArg (Pattern.ex bound) hp
  | all bound p hp => exact congrArg (Pattern.all bound) hp
  | mu p hp => exact congrArg Pattern.mu hp
  | nu p hp => exact congrArg Pattern.nu hp

theorem Pattern.map_comp (f : A ⟶ B) (g : B ⟶ C) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    p.map (f ≫ g) = (p.map f).map g := by
  induction p with
  | base p => exact congrArg Pattern.base (FirstOrder.Pattern.map_comp f g p)
  | setvar => rfl
  | app op args ih => exact congrArg (Pattern.app _) (funext ih)
  | dualApp op args ih => exact congrArg (Pattern.dualApp _) (funext ih)
  | conj p q hp hq => exact congrArg₂ Pattern.conj hp hq
  | disj p q hp hq => exact congrArg₂ Pattern.disj hp hq
  | ex bound p hp => exact congrArg (Pattern.ex bound) hp
  | all bound p hp => exact congrArg (Pattern.all bound) hp
  | mu p hp => exact congrArg Pattern.mu hp
  | nu p hp => exact congrArg Pattern.nu hp

theorem Pattern.denote_map (f : A ⟶ B) (M : Model B) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s)
    (v : ObjEnv B M Γ) :
    (p.map f).denote M v = p.denote (FirstOrder.SignatureMap.reduct f M) v := by
  induction p with
  | base p =>
      apply OrderHom.ext
      funext η
      exact FirstOrder.SignatureMap.denote_map f M p v
  | setvar => rfl
  | app op args ih =>
      apply OrderHom.ext
      funext η
      change application M (f.operations op) (fun i => (args i |>.map f).denote M v η) = _
      simp only [ih]
      rfl
  | dualApp op args ih =>
      apply OrderHom.ext
      funext η
      change dualApplication M (f.operations op) (fun i => (args i |>.map f).denote M v η) = _
      simp only [ih]
      rfl
  | conj p q hp hq =>
      apply OrderHom.ext
      funext η
      change (p.map f).denote M v η ∩ (q.map f).denote M v η = _
      rw [hp, hq]
      rfl
  | disj p q hp hq =>
      apply OrderHom.ext
      funext η
      change (p.map f).denote M v η ∪ (q.map f).denote M v η = _
      rw [hp, hq]
      rfl
  | ex bound p hp =>
      apply OrderHom.ext
      funext η
      change {x | ∃ a : M.carrier bound, x ∈ (p.map f).denote M (Fin.cases a v) η} = _
      simp only [hp]
      rfl
  | all bound p hp =>
      apply OrderHom.ext
      funext η
      change {x | ∀ a : M.carrier bound, x ∈ (p.map f).denote M (Fin.cases a v) η} = _
      simp only [hp]
      rfl
  | mu p hp =>
      apply OrderHom.ext
      funext η
      change (((p.map f).denote M v).comp (insert _ M η)).lfp = _
      rw [hp]
      rfl
  | nu p hp =>
      apply OrderHom.ext
      funext η
      change (((p.map f).denote M v).comp (insert _ M η)).gfp = _
      rw [hp]
      rfl

variable (M : Model A) {r k : Nat} {P' : Fin (r+1) → S} {Γ : Fin k → S}
    (p : Pattern A P' Γ (P' 0)) (v : ObjEnv A M Γ) (η : SetEnv A M (P' ∘ Fin.succ))

theorem mu_unfold :
    (Pattern.mu p).denote M v η = p.denote M v (Fin.cases ((Pattern.mu p).denote M v η) η) :=
  ((p.denote M v).comp (insert A M η)).map_lfp.symm

theorem mu_induction (X : Set (M.carrier (P' 0)))
    (h : p.denote M v (Fin.cases X η) ⊆ X) : (Pattern.mu p).denote M v η ⊆ X :=
  ((p.denote M v).comp (insert A M η)).lfp_le h

theorem nu_unfold :
    (Pattern.nu p).denote M v η = p.denote M v (Fin.cases ((Pattern.nu p).denote M v η) η) :=
  ((p.denote M v).comp (insert A M η)).map_gfp.symm

theorem nu_coinduction (X : Set (M.carrier (P' 0)))
    (h : X ⊆ p.denote M v (Fin.cases X η)) : X ⊆ (Pattern.nu p).denote M v η :=
  ((p.denote M v).comp (insert A M η)).le_gfp h

end Silmaril.Logic.Matching.FixedPoint
