module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual.Systems.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual.Finite

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory

universe u

/-- Actual finite set towers validate the compiled source inference presentation. -/
theorem logic_sound (levels : ℕ) : (logic.{u} levels).Sound := by
  intro S H j d T hT
  apply d.compile.sound (Discrete.as T)
  rintro q ⟨p, ⟨φ, hφ, rfl⟩, rfl⟩
  exact hT φ hφ

@[simp] theorem encode_ordinary (levels : ℕ) (j : W.Finite.Sentence levels) :
    encodeSentence levels (ordinarySentence levels j) = j := rfl

/-- The forward-then-backward syntax map is an exact retraction on ordinary W. -/
theorem fromW_toW (levels : ℕ) :
    Inst.CoHom.comp (fromW.{u} levels) (toW levels) = Inst.CoHom.id (W.Finite.bundled.{u} levels) := rfl

/-- Each source model has an expansion along compilation by the identical finite tower. -/
theorem toW_modelExpansive (levels : ℕ) : (toW.{u} levels).ModelExpansive := by
  intro S T
  exact ⟨T, rfl⟩

theorem fromW_modelExpansive (levels : ℕ) : (fromW.{u} levels).ModelExpansive := by
  intro S T
  exact ⟨T, rfl⟩

/-- Borrow semantic entailment along the actual mutual-to-W sentence compilation. -/
theorem entails_iff (levels : ℕ) (H : Set (Sentence levels)) (j : Sentence levels) :
    (room.{u} levels).Entails H j ↔
      (W.Finite.room.{u} levels).Entails (encodeSentence levels '' H) (encodeSentence levels j) :=
  (toW levels).entails_iff (toW_modelExpansive levels) (Discrete.mk ()) H j

/-- Compilation commutes with increasing the finite count. -/
theorem toW_include {n m : ℕ} (h : n ≤ m) :
    Inst.CoHom.comp (inclusion.{u} h) (toW m) =
      Inst.CoHom.comp (toW n) (W.Finite.inclusion h) := rfl

theorem toIndexed_include {n m : ℕ} (h : n ≤ m) :
    Inst.CoHom.comp (inclusion.{u} h) (toIndexed m) =
      Inst.CoHom.comp (toIndexed n) (Indexed.Finite.inclusion h) := rfl

/-- The institution map compiles the same source term through either route. -/
theorem toIndexed_toW (levels : ℕ) :
    Inst.CoHom.comp (toIndexed.{u} levels) (Indexed.Finite.toW levels) = toW levels := rfl

theorem toIndexed_modelExpansive (levels : ℕ) : (toIndexed.{u} levels).ModelExpansive := by
  intro S T
  exact ⟨T, rfl⟩

theorem indexed_entails_iff (levels : ℕ) (H : Set (Sentence levels)) (j : Sentence levels) :
    (room.{u} levels).Entails H j ↔
      (Indexed.Finite.room.{u} levels).Entails (indexedSentence levels '' H) (indexedSentence levels j) :=
  (toIndexed levels).entails_iff (toIndexed_modelExpansive levels) (Discrete.mk ()) H j

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual.Finite
