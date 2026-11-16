module

public import Silmaril.Logic.Matching.GeneralFixedPoint.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open CategoryTheory
open Algebraic.ManySorted (Signature)
variable {S : Type} {A B C : Signature S}

theorem Pattern.map_id {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S}
    (p : Pattern A P Γ s) : p.map (𝟙 A) = p := by
  induction p with
  | base p => exact congrArg Pattern.base (FirstOrder.Pattern.map_id p)
  | setvar => rfl
  | app op _ ih => exact congrArg (Pattern.app op) (funext ih)
  | neg _ ih => exact congrArg Pattern.neg ih
  | conj _ _ hp hq => exact congrArg₂ Pattern.conj hp hq
  | ex b _ ih => exact congrArg (Pattern.ex b) ih
  | mu _ ih => exact congrArg Pattern.mu ih
  | nu _ ih => exact congrArg Pattern.nu ih

theorem Pattern.map_comp (f : A ⟶ B) (g : B ⟶ C) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    p.map (f ≫ g) = (p.map f).map g := by
  induction p with
  | base p => exact congrArg Pattern.base (FirstOrder.Pattern.map_comp f g p)
  | setvar => rfl
  | app op _ ih => exact congrArg (Pattern.app _) (funext ih)
  | neg _ ih => exact congrArg Pattern.neg ih
  | conj _ _ hp hq => exact congrArg₂ Pattern.conj hp hq
  | ex b _ ih => exact congrArg (Pattern.ex b) ih
  | mu _ ih => exact congrArg Pattern.mu ih
  | nu _ ih => exact congrArg Pattern.nu ih

theorem Pattern.occurs_map (f : A ⟶ B) {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    (p.map f).occurs = p.occurs := by
  induction p with
  | base _ | setvar _ => rfl
  | app op args ih =>
      change (fun n i => (List.finRange _).any (fun j => ((args j).map f).occurs n i)) = _
      simp only [ih]
      rfl
  | neg p ih =>
      change (fun n i => (p.map f).occurs (!n) i) = _
      rw [ih]; rfl
  | conj p q hp hq =>
      change (fun n i => (p.map f).occurs n i || (q.map f).occurs n i) = _
      rw [hp, hq]; rfl
  | ex b p ih => exact ih
  | mu p ih | nu p ih =>
      change (fun n i => (p.map f).occurs n (Fin.succ i)) = _
      rw [ih]; rfl

theorem Pattern.admissible_map (f : A ⟶ B) {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    (p.map f).admissible = p.admissible := by
  induction p with
  | base _ | setvar _ => rfl
  | app op args ih =>
      change (List.finRange _).all (fun j => ((args j).map f).admissible) = _
      simp only [ih]
      rfl
  | neg p ih | ex _ p ih => exact ih
  | conj p q hp hq =>
      change ((p.map f).admissible && (q.map f).admissible) = _
      rw [hp, hq]; rfl
  | mu p ih | nu p ih =>
      change ((p.map f).admissible && !(p.map f).occurs true 0) = _
      rw [ih, occurs_map]; rfl

theorem Pattern.denote_map (f : A ⟶ B) (M : Model B) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ (v : ObjEnv B M Γ) (η : SetEnv B M P),
      (p.map f).denote M v η = p.denote (FirstOrder.SignatureMap.reduct f M) v η := by
  induction p with
  | base p => intro v η; exact FirstOrder.SignatureMap.denote_map f M p v
  | setvar _ => intro _ _; rfl
  | app op args ih =>
      intro v η
      change FixedPoint.application M (f.operations op)
        (fun i => ((args i).map f).denote M v η) = _
      simp only [ih]
      rfl
  | neg p ih =>
      intro v η
      change ((p.map f).denote M v η)ᶜ = _
      rw [ih]; rfl
  | conj p q hp hq =>
      intro v η
      change (p.map f).denote M v η ∩ (q.map f).denote M v η = _
      rw [hp, hq]; rfl
  | ex b p ih =>
      intro v η
      change {x | ∃ a : M.carrier b, x ∈ (p.map f).denote M (Fin.cases a v) η} = _
      simp only [ih]
      rfl
  | mu p ih =>
      intro v η
      change sInf {X | (p.map f).denote M v (Fin.cases X η) ⊆ X} = _
      simp only [ih]
      rfl
  | nu p ih =>
      intro v η
      change sSup {X | X ⊆ (p.map f).denote M v (Fin.cases X η)} = _
      simp only [ih]
      rfl
end Silmaril.Logic.Matching.GeneralFixedPoint
