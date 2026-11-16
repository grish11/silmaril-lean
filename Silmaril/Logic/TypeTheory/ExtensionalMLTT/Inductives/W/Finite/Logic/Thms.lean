module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Logic.Defs

@[expose] public section

/-! Finite-tower models validate the uniformly bounded inference calculus. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite

open Silmaril.Logic.Institution.Metatheory

universe u

/-- The finite logical system is sound in every finite-tower model. -/
theorem logic_sound (levels : ℕ) : (logic.{u} levels).Sound := by
  intro S H j d T hT
  apply d.sound (CategoryTheory.Discrete.as T)
  rintro q ⟨φ, hφ, rfl⟩
  exact hT φ hφ

/-- Forgetting proof theory recovers the existing finite-universe institution. -/
@[simp] theorem logic_toInst (levels : ℕ) : (logic.{u} levels).toInst = bundled.{u} levels := rfl

/-- Logical inclusions use the existing institution sentence maps and model reducts. -/
@[simp] theorem inclusionLogical_toInstCoHom {n m : ℕ} (h : n ≤ m) :
    (inclusionLogical.{u} h).toInstCoHom = inclusion.{u} h := rfl

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite
