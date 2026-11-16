module

public import Silmaril.Logic.Matching.GeneralFixedPoint.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open CategoryTheory
open Algebraic.ManySorted (Signature)
variable {S : Type} {A : Signature S}

theorem ofPositive_no_negative {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S}
    (p : FixedPoint.Pattern A P Γ s) : ∀ i, (ofPositive p).occurs true i = false := by
  induction p with
  | base _ | setvar _ => intro _; rfl
  | app op args ih | dualApp op args ih =>
      intro i
      change (List.finRange _).any (fun j => (ofPositive (args j)).occurs true i) = false
      simp only [ih]
      simp
  | conj p q hp hq | disj p q hp hq =>
      intro i
      change ((ofPositive p).occurs true i || (ofPositive q).occurs true i) = false
      rw [hp, hq]; rfl
  | ex _ p ih | all _ p ih => exact ih
  | mu _ ih | nu _ ih => intro i; exact ih i.succ

theorem ofPositive_admissible {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S}
    (p : FixedPoint.Pattern A P Γ s) : (ofPositive p).admissible = true := by
  induction p with
  | base _ | setvar _ => rfl
  | app op args ih | dualApp op args ih =>
      change (List.finRange _).all (fun j => (ofPositive (args j)).admissible) = true
      simp only [ih]
      simp
  | conj p q hp hq | disj p q hp hq =>
      change (ofPositive p).admissible && (ofPositive q).admissible = true
      rw [hp, hq]; rfl
  | ex _ p ih | all _ p ih => exact ih
  | mu p ih | nu p ih =>
      change (ofPositive p).admissible && !(ofPositive p).occurs true 0 = true
      rw [ih, ofPositive_no_negative]; rfl

theorem denote_ofPositive (M : Model A) {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (p : FixedPoint.Pattern A P Γ s) :
    ∀ (v : ObjEnv A M Γ) (η : SetEnv A M P),
      (ofPositive p).denote M v η = p.denote M v η := by
  induction p with
  | base _ | setvar _ => intros; rfl
  | app op args ih =>
      intro v η
      change FixedPoint.application M op (fun i => (ofPositive (args i)).denote M v η) = _
      simp only [ih]
      rfl
  | dualApp op args ih =>
      intro v η
      change (FixedPoint.application M op
        (fun i => ((ofPositive (args i)).denote M v η)ᶜ))ᶜ = _
      simp only [ih]
      rfl
  | conj p q hp hq =>
      intro v η
      change (ofPositive p).denote M v η ∩ (ofPositive q).denote M v η = _
      rw [hp, hq]; rfl
  | disj p q hp hq =>
      intro v η
      change (((ofPositive p).denote M v η)ᶜ ∩ ((ofPositive q).denote M v η)ᶜ)ᶜ = _
      rw [hp, hq, ← Set.compl_union, compl_compl]
      rfl
  | ex b p ih =>
      intro v η
      change {x | ∃ a : M.carrier b, x ∈ (ofPositive p).denote M (Fin.cases a v) η} = _
      simp only [ih]
      rfl
  | all b p ih =>
      intro v η
      change {x | ∃ a : M.carrier b, x ∉ (ofPositive p).denote M (Fin.cases a v) η}ᶜ = _
      simp only [ih]
      ext x
      change (¬ ∃ a : M.carrier b, x ∉ p.denote M (Fin.cases a v) η) ↔
        ∀ a : M.carrier b, x ∈ p.denote M (Fin.cases a v) η
      simp
  | mu p ih =>
      intro v η
      change sInf {X | (ofPositive p).denote M v (Fin.cases X η) ⊆ X} = _
      simp only [ih]
      rfl
  | nu p ih =>
      intro v η
      change sSup {X | X ⊆ (ofPositive p).denote M v (Fin.cases X η)} = _
      simp only [ih]
      rfl
theorem ofPositive_map {B : Signature S} (f : A ⟶ B) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : FixedPoint.Pattern A P Γ s) :
    ofPositive (p.map f) = (ofPositive p).map f := by
  induction p with
  | base _ | setvar _ => rfl
  | app op args ih => exact congrArg (Pattern.app (f.operations op)) (funext ih)
  | dualApp op args ih =>
      apply congrArg Pattern.neg
      apply congrArg (Pattern.app (f.operations op))
      exact funext fun i => congrArg Pattern.neg (ih i)
  | conj p q hp hq => exact congrArg₂ Pattern.conj hp hq
  | disj p q hp hq =>
      apply congrArg Pattern.neg
      exact congrArg₂ Pattern.conj (congrArg Pattern.neg hp) (congrArg Pattern.neg hq)
  | ex b p ih => exact congrArg (Pattern.ex b) ih
  | all b p ih =>
      apply congrArg Pattern.neg
      exact congrArg (Pattern.ex b) (congrArg Pattern.neg ih)
  | mu p ih => exact congrArg Pattern.mu ih
  | nu p ih => exact congrArg Pattern.nu ih

end Silmaril.Logic.Matching.GeneralFixedPoint
