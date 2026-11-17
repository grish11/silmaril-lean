module

public import Silmaril.Containers.Cas.Defs

/-!
# Proofs: content-addressed stores

Proofs for `Silmaril.Containers.Cas.Thms`. Nothing imports this module except that header.
-/

public section

namespace Silmaril.Proofs.Containers.Cas

open Silmaril.Containers.Cas

variable {D C C' : Type}

theorem sound_put [DecidableEq D] {h : C → D} {S : Store D C} (hS : Store.Sound h S) (c : C) :
    Store.Sound h (S.put h c) := by
  intro d c' hc
  unfold Store.put Store.insert at hc
  split at hc
  · rename_i hd; cases hc; exact hd.symm
  · exact hS d c' hc

theorem sound_checked [DecidableEq D] (h : C → D) (S : Store D C) : Store.Sound h (S.checked h) := by
  intro d c hc
  unfold Store.checked at hc
  split at hc
  · split at hc
    · cases hc; assumption
    · cases hc
  · cases hc

theorem checked_of_sound [DecidableEq D] {h : C → D} {S : Store D C} (hS : Store.Sound h S) :
    S.checked h = S := by
  funext d
  unfold Store.checked
  split <;> rename_i heq
  · simp [hS d _ heq, heq]
  · exact heq.symm

theorem sound_decode {h : C → D} {S : Store D C} (hS : Store.Sound h S) {dec : C → Option C'}
    {enc : C' → C} (hinv : ∀ c x, dec c = some x → enc x = c) :
    Store.Sound (h ∘ enc) (S.decode dec) := by
  intro d x hx
  unfold Store.decode at hx
  cases hSd : S d with
  | none => rw [hSd] at hx; cases hx
  | some c =>
    rw [hSd] at hx
    simp only [Function.comp, hinv c x hx]
    exact hS d c hSd

end Silmaril.Proofs.Containers.Cas
