module

public import Silmaril.Logic.Matching.GeneralFixedPoint.Variables.Defs

@[expose] public section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open Algebraic.ManySorted (Signature)
open FixedPoint (Ren)
variable {S : Type}

theorem Pattern.occurs_renameObjects {A : Signature S} {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {l : Nat} {Δ : Fin l → S} (ρ : Ren Γ Δ) (n : Bool) (i : Fin r),
      (p.renameObjects ρ).occurs n i = p.occurs n i := by
  induction p with
  | base => intros; rfl
  | setvar => intros; rfl
  | app op args ih =>
      intro l Δ ρ n i
      change (List.finRange _).any (fun x => ((args x).renameObjects ρ).occurs n i) = _
      simp only [ih]
      rfl
  | neg p hp => intro l Δ ρ n i; exact hp ρ (!n) i
  | conj p q hp hq =>
      intro l Δ ρ n i
      exact congrArg₂ Bool.or (hp ρ n i) (hq ρ n i)
  | ex b p hp => intros; exact hp _ _ _
  | mu p hp => intros; exact hp _ _ _
  | nu p hp => intros; exact hp _ _ _

theorem Pattern.admissible_renameObjects {A : Signature S} {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {l : Nat} {Δ : Fin l → S} (ρ : Ren Γ Δ),
      (p.renameObjects ρ).admissible = p.admissible := by
  induction p with
  | base => intros; rfl
  | setvar => intros; rfl
  | app op args ih =>
      intro l Δ ρ
      change (List.finRange _).all (fun x => ((args x).renameObjects ρ).admissible) = _
      simp only [ih]
      rfl
  | neg p hp => intros; exact hp _
  | conj p q hp hq =>
      intro l Δ ρ
      exact congrArg₂ Bool.and (hp ρ) (hq ρ)
  | ex b p hp => intros; exact hp _
  | mu p hp =>
      intro l Δ ρ
      change ((p.renameObjects ρ).admissible && !(p.renameObjects ρ).occurs true 0) = _
      rw [hp, occurs_renameObjects]
      rfl
  | nu p hp =>
      intro l Δ ρ
      change ((p.renameObjects ρ).admissible && !(p.renameObjects ρ).occurs true 0) = _
      rw [hp, occurs_renameObjects]
      rfl

theorem occurs_setvar_cast {A : Signature S} {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (x : Fin r) (h : P x = s) (n : Bool) (i : Fin r) :
    (h ▸ Pattern.setvar (A := A) (P := P) (Γ := Γ) x).occurs n i = (!n && i == x) := by
  cases h
  rfl

/-- A renaming with exactly one source coordinate mapping to the queried target
coordinate preserves the two polarities at that coordinate. -/
theorem Pattern.occurs_renameSets_coordinate {A : Signature S} {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {a : Nat} {Q : Fin a → S} (ρ : Ren P Q) (i : Fin r) (j : Fin a),
      (∀ x, (j == (ρ x).val) = (i == x)) → ∀ n,
      (p.renameSets ρ).occurs n j = p.occurs n i := by
  induction p with
  | base => intros; rfl
  | setvar x =>
      intro a Q ρ i j h n
      dsimp only [Pattern.renameSets]
      rw [occurs_setvar_cast, h]
      rfl
  | app op args ih =>
      intro a Q ρ i j h n
      change (List.finRange _).any (fun x => ((args x).renameSets ρ).occurs n j) = _
      simp only [fun x => ih x ρ i j h n]
      rfl
  | neg p hp => intro a Q ρ i j h n; exact hp ρ i j h (!n)
  | conj p q hp hq =>
      intro a Q ρ i j h n
      exact congrArg₂ Bool.or (hp ρ i j h n) (hq ρ i j h n)
  | ex b p hp => intro a Q ρ i j h n; exact hp ρ i j h n
  | mu p hp =>
      intro a Q ρ i j h n
      apply hp (Ren.liftHead ρ) i.succ j.succ
      intro x
      exact Fin.cases rfl (fun y => by simpa [Ren.liftHead] using h y) x
  | nu p hp =>
      intro a Q ρ i j h n
      apply hp (Ren.liftHead ρ) i.succ j.succ
      intro x
      exact Fin.cases rfl (fun y => by simpa [Ren.liftHead] using h y) x

/-- A target coordinate outside the image of a renaming cannot occur. -/
theorem Pattern.occurs_renameSets_absent {A : Signature S} {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {a : Nat} {Q : Fin a → S} (ρ : Ren P Q) (j : Fin a),
      (∀ x, (j == (ρ x).val) = false) → ∀ n,
      (p.renameSets ρ).occurs n j = false := by
  induction p with
  | base => intros; rfl
  | setvar x =>
      intro a Q ρ j h n
      dsimp only [Pattern.renameSets]
      rw [occurs_setvar_cast, h]
      exact Bool.and_false _
  | app op args ih =>
      intro a Q ρ j h n
      change (List.finRange _).any (fun x => ((args x).renameSets ρ).occurs n j) = false
      simp only [fun x => ih x ρ j h n]
      simp
  | neg p hp => intro a Q ρ j h n; exact hp ρ j h (!n)
  | conj p q hp hq =>
      intro a Q ρ j h n
      change ((p.renameSets ρ).occurs n j || (q.renameSets ρ).occurs n j) = false
      rw [hp ρ j h, hq ρ j h]
      rfl
  | ex b p hp => intro a Q ρ j h n; exact hp ρ j h n
  | mu p hp =>
      intro a Q ρ j h n
      apply hp (Ren.liftHead ρ) j.succ
      intro x
      exact Fin.cases rfl (fun y => by simpa [Ren.liftHead] using h y) x
  | nu p hp =>
      intro a Q ρ j h n
      apply hp (Ren.liftHead ρ) j.succ
      intro x
      exact Fin.cases rfl (fun y => by simpa [Ren.liftHead] using h y) x

theorem Pattern.occurs_shiftSets_succ {A : Signature S} {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s b : S} (p : Pattern A P Γ s)
    (n : Bool) (i : Fin r) :
    (p.renameSets (Ren.shift P b)).occurs n i.succ = p.occurs n i :=
  p.occurs_renameSets_coordinate _ i i.succ (fun _ => by simp [Ren.shift]) n

theorem Pattern.occurs_shiftSets_zero {A : Signature S} {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s b : S} (p : Pattern A P Γ s) (n : Bool) :
    (p.renameSets (Ren.shift P b)).occurs n 0 = false :=
  p.occurs_renameSets_absent _ 0 (fun _ => rfl) n

theorem admissible_setvar_cast {A : Signature S} {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (x : Fin r) (h : P x = s) :
    (h ▸ Pattern.setvar (A := A) (P := P) (Γ := Γ) x).admissible = true := by
  cases h
  rfl

theorem Pattern.admissible_renameSets {A : Signature S} {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {a : Nat} {Q : Fin a → S} (ρ : Ren P Q),
      (p.renameSets ρ).admissible = p.admissible := by
  induction p with
  | base => intros; rfl
  | setvar x =>
      intro a Q ρ
      exact admissible_setvar_cast (ρ x).val (ρ x).property
  | app op args ih =>
      intro a Q ρ
      change (List.finRange _).all (fun x => ((args x).renameSets ρ).admissible) = _
      simp only [ih]
      rfl
  | neg p hp => intros; exact hp _
  | conj p q hp hq =>
      intro a Q ρ
      exact congrArg₂ Bool.and (hp ρ) (hq ρ)
  | ex b p hp => intros; exact hp _
  | mu p hp =>
      intro a Q ρ
      change ((p.renameSets (Ren.liftHead ρ)).admissible &&
        !(p.renameSets (Ren.liftHead ρ)).occurs true 0) = _
      rw [hp, p.occurs_renameSets_coordinate (Ren.liftHead ρ) 0 0
        (fun x => Fin.cases rfl (fun _ => rfl) x)]
      rfl
  | nu p hp =>
      intro a Q ρ
      change ((p.renameSets (Ren.liftHead ρ)).admissible &&
        !(p.renameSets (Ren.liftHead ρ)).occurs true 0) = _
      rw [hp, p.occurs_renameSets_coordinate (Ren.liftHead ρ) 0 0
        (fun x => Fin.cases rfl (fun _ => rfl) x)]
      rfl

end Silmaril.Logic.Matching.GeneralFixedPoint
