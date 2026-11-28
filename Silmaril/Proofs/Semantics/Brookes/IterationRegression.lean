module

import Silmaril.Semantics.Brookes.Iteration.Thms

namespace Silmaril.Semantics.Brookes

open Behavior

private def writeThenRead : Bool → Behavior Nat (Nat ⊕ Bool)
  | false => atomic fun _ t result => t = 1 ∧ result = .inr true
  | true => atomic fun s t result => t = s ∧ result = .inl s

-- One call cannot return from the initial state.
example : ¬(approx writeThenRead 1 false).completes 0 1 1 := by
  intro h
  obtain ⟨_, _, s, hWrite, hNext, _⟩ := bind_accepts_iff.mp h
  obtain ⟨_, _, ⟨_, rfl⟩, _⟩ := atomic_accepts_iff.mp hWrite
  exact hNext

-- Two calls suffice, and the read observes the store written by the first call.
example : (iterate writeThenRead false).completes 0 1 1 := by
  refine ⟨2, ?_⟩
  apply bind_completes_iff.mpr
  refine ⟨1, .inr true, atomic_completes_iff.mpr ⟨rfl, rfl⟩, ?_⟩
  apply bind_completes_iff.mpr
  exact ⟨1, .inl 1, atomic_completes_iff.mpr ⟨rfl, rfl⟩,
    atomic_completes_iff.mpr ⟨rfl, rfl⟩⟩

private def writeForever : Unit → Behavior Nat (Nat ⊕ Unit) :=
  fun _ => atomic fun _ t result => t = 1 ∧ result = .inr ()

-- An effectful loop without a return path is indistinguishable from bottom
-- for all open completed observations, even though its body writes.
example : iterate writeForever = ⊥ := by
  apply iterate_inr_eq_bot
  intro _ _ _ h
  obtain ⟨_, _, ⟨_, eq⟩, _⟩ := atomic_accepts_iff.mp h
  cases eq

example : (writeForever ()).completes 0 1 (.inr ()) :=
  atomic_completes_iff.mpr ⟨rfl, rfl⟩

example : ret 1 ≠ (⊥ : Behavior Nat Nat) := ret_ne_bot 0 1

example : Elgot.LawfulElgotMonad (Behavior Nat) := inferInstance

end Silmaril.Semantics.Brookes
