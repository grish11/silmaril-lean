module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual.Apex.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual.Apex

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory

universe u

theorem logic_sound : logic.{u}.Sound := by
  intro S H j d T hT
  apply W.Ctx.JEqH.sound (Discrete.as T) ?_ d.compile
  rintro q ⟨p, ⟨φ, hφ, rfl⟩, rfl⟩
  exact hT φ hφ

@[simp] theorem encode_ordinary (j : W.Institution.Sentence.{u}) : encodeSentence (ordinarySentence j) = j := rfl

theorem fromW_toW : Inst.CoHom.comp fromW.{u} toW = Inst.CoHom.id W.Institution.bundled.{u} := rfl

theorem toW_modelExpansive : toW.{u}.ModelExpansive := by
  intro S T
  exact ⟨T, rfl⟩

theorem fromW_modelExpansive : fromW.{u}.ModelExpansive := by
  intro S T
  exact ⟨T, rfl⟩

theorem toIndexed_modelExpansive : toIndexed.{u}.ModelExpansive := by
  intro S T
  exact ⟨T, rfl⟩

theorem toIndexed_toW :
    Inst.CoHom.comp toIndexed.{u} Indexed.Apex.toW = toW := rfl

theorem indexed_entails_iff (H : Set Sentence.{u}) (j : Sentence.{u}) :
    room.Entails H j ↔ Indexed.Apex.room.Entails (indexedSentence '' H) (indexedSentence j) :=
  toIndexed.entails_iff toIndexed_modelExpansive (Discrete.mk ()) H j

theorem entails_iff (H : Set Sentence.{u}) (j : Sentence.{u}) :
    room.Entails H j ↔ W.Institution.room.Entails (encodeSentence '' H) (encodeSentence j) :=
  toW.entails_iff toW_modelExpansive (Discrete.mk ()) H j

/-- The explicitly lifted fixed stage has exactly the original finite interpretation. -/
theorem Stage.logic_sound (levels : ℕ) : (Stage.logic.{u} levels).Sound := by
  intro S H j d T hT
  apply d.compile.sound (Discrete.as T)
  rintro q ⟨p, ⟨φ, hφ, rfl⟩, rfl⟩
  exact hT φ hφ

/-- Explicit universe lifting preserves exactly the original finite-stage satisfaction. -/
theorem Stage.satisfaction_iff (levels : ℕ) (T : (Stage.room.{u} levels).Mod)
    (j : Stage.Sentence.{u} levels) :
    (Stage.room levels).Sat T j ↔ (Mutual.Finite.room levels).Sat T j.down := Iff.rfl

/-- Explicit universe lifting preserves and reflects the original finite proof relation. -/
theorem Stage.derives_iff (levels : ℕ) (H : Set (Stage.Sentence.{u} levels))
    (j : Stage.Sentence.{u} levels) :
    (Stage.logic levels).Derives (Discrete.mk ()) H j ↔
      (Mutual.Finite.logic levels).Derives (Discrete.mk ()) (ULift.down '' H) j.down := by
  change Mutual.Consequence levels ((fun q => q.down.val) '' H) j.down.val ↔
    Mutual.Consequence levels (Subtype.val '' (ULift.down '' H)) j.down.val
  rw [← Set.image_comp]
  rfl

/-- The stage-to-apex map preserves semantic consequence. Reflection would require
an additional expansion property for arbitrary finite models. -/
theorem Stage.entails_toApex (levels : ℕ) {H : Set (Stage.Sentence.{u} levels)}
    {j : Stage.Sentence.{u} levels} (d : (Stage.room levels).Entails H j) :
    Apex.room.Entails (Stage.apexSentence levels '' H) (Stage.apexSentence levels j) :=
  (Stage.toApex levels).entails_map (S := Discrete.mk ()) d

/-- Finite count inclusions commute with their genuine hierarchy-apex map. -/
theorem Stage.toApex_include {n m : ℕ} (h : n ≤ m) :
    Inst.CoHom.comp (Stage.inclusion.{u} h) (Stage.toApex m) = Stage.toApex.{u} n := rfl

/-- Finite mutual flattening commutes with passage to the hierarchy apices. -/
theorem Stage.toIndexed_toApex (levels : ℕ) :
    Inst.CoHom.comp (Stage.toIndexed.{u} levels) (Indexed.Apex.Stage.toApex levels) =
      Inst.CoHom.comp (Stage.toApex levels) Apex.toIndexed := rfl

theorem Stage.toIndexed_include {n m : ℕ} (h : n ≤ m) :
    Inst.CoHom.comp (Stage.inclusion.{u} h) (Stage.toIndexed m) =
      Inst.CoHom.comp (Stage.toIndexed n) (Indexed.Apex.Stage.inclusion h) := rfl

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual.Apex
