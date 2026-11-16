module

public import Silmaril.Logic.Kore.Modules.Checking.Thms

@[expose] public section
namespace Silmaril.Proofs.Logic.Kore.Modules.Fuel
open Silmaril.Logic.Kore.Modules

/-- Success extension preserves the exact value, including dependent proof fields. -/
def Extends {α : Type} (a b : Option α) : Prop := ∀ x, a = some x → b = some x

theorem extends_refl {α : Type} (a : Option α) : Extends a a := fun _ h => h

theorem extends_bind {α β : Type} {a b : Option α} {f g : α → Option β}
    (h : Extends a b) (step : ∀ x, Extends (f x) (g x)) :
    Extends (a.bind f) (b.bind g) := by
  intro y accepted
  obtain ⟨x, hx, hy⟩ := Option.bind_eq_some_iff.mp accepted
  rw [h x hx]
  exact step x y hy

theorem extends_map {α β : Type} {a b : Option α} (f : α → β)
    (h : Extends a b) : Extends (a.map f) (b.map f) := by
  intro y accepted
  cases ha : a with
  | none => simp [ha] at accepted
  | some x => simpa only [ha, h x ha] using accepted

theorem extends_mapM {α β : Type} (xs : List α) (f g : α → Option β)
    (step : ∀ x, Extends (f x) (g x)) : Extends (xs.mapM f) (xs.mapM g) := by
  induction xs with
  | nil => exact extends_refl _
  | cons x xs ih =>
      simp only [List.mapM_cons]
      apply extends_bind (step x)
      intro y
      apply extends_bind ih
      intro ys
      exact extends_refl _

theorem extends_collect {n : Nat} {α : Fin n → Type}
    (f g : (i : Fin n) → Option (α i)) (step : ∀ i, Extends (f i) (g i)) :
    Extends (Checking.collect f) (Checking.collect g) := by
  induction n with
  | zero => exact extends_refl _
  | succ n ih =>
      simp only [Checking.collect]
      apply extends_bind (step 0)
      intro x
      apply extends_bind (ih _ _ (fun i => step i.succ))
      intro xs
      exact extends_refl _

theorem freeVariables_add (fuel extra : Nat) : ∀ bound raw,
    Extends (Checking.freeVariables bound fuel raw)
      (Checking.freeVariables bound (fuel + extra) raw) := by
  induction fuel with
  | zero => intro bound raw names h; contradiction
  | succ n ih =>
      intro bound raw
      cases raw <;> simp only [Nat.succ_add, Checking.freeVariables]
      all_goals first
        | exact extends_refl _
        | exact ih _ _
        | apply extends_bind (ih _ _); intro x
          apply extends_bind (ih _ _); intro y
          exact extends_refl _
        | exact extends_map _ (extends_mapM _ _ _ (fun p => ih bound p))
end Silmaril.Proofs.Logic.Kore.Modules.Fuel
