module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Logic.Defs

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedFiniteLogic

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.SetTheory
open Silmaril.Logic.TypeTheory.ExtensionalMLTT Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite

universe u

/-- Actual bounded target soundness proves soundness of its finite logical system. -/
theorem logic_sound (n : ℕ) : (logic.{u} n).Sound := by
  intro S H j h T hT
  apply h.sound T.as
  rintro q ⟨k, hk, rfl⟩
  exact hT k hk

/-- An actual supplied finite target model refutes the bounded Empty sentence. -/
theorem logic_consistent (n : ℕ) [HasFiniteTower.{u} n] :
    ((logic.{u} n).er (Discrete.mk ())).Consistent ∅ := by
  refine ⟨emptySentence n, ?_⟩
  intro h
  have hd : ECtx.JEqB n (Subtype.val '' (∅ : Set (Sentence n))) .nil .empty .zero .zero := h
  have hc : ECtx.JEqB n ∅ .nil .empty .zero .zero := by simpa only [Set.image_empty] using hd
  exact ECtx.JEqB.no_closed_empty (HasFiniteTower.tower.{u} n) hc

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedFiniteLogic
