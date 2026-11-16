module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Systems.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory

universe u

/-- W inference is sound in each supplied hierarchy. -/
theorem Institution.logic_sound : Institution.logic.{u}.Sound := by
  intro S H j d T hT
  apply Ctx.JEqH.sound (Discrete.as T) ?_ d
  rintro q ⟨φ, hφ, rfl⟩
  exact hT φ hφ

@[simp] theorem Embedding.finiteLogical_toInstCoHom (levels : ℕ) :
    (finiteLogical.{u} levels).toInstCoHom = finiteInclusion.{u} levels := rfl

@[simp] theorem Embedding.hierarchyLogical_toInstCoHom :
    hierarchyLogical.{u}.toInstCoHom = hierarchyInclusion.{u} := rfl

/-- Every finite model expands along the base-to-W inclusion by the identical tower. -/
theorem Embedding.finiteInclusion_modelExpansive (levels : ℕ) :
    (finiteInclusion.{u} levels).ModelExpansive := by
  intro S T
  exact ⟨T, rfl⟩

/-- Every hierarchy model expands along the base-to-W inclusion by itself. -/
theorem Embedding.hierarchyInclusion_modelExpansive :
    hierarchyInclusion.{u}.ModelExpansive := by
  intro S T
  exact ⟨T, rfl⟩

/-- Both routes around a finite universe-count square translate the same sentence. -/
theorem Embedding.finiteSentence_include {n m : ℕ} (h : n ≤ m)
    (j : ExtensionalMLTT.Finite.Sentence n) :
    finiteSentence m (ExtensionalMLTT.Finite.includeSentence h j) =
      Finite.includeSentence h (finiteSentence n j) := rfl

/-- The institution square for increasing the count and adding W commutes. -/
theorem Embedding.finiteInclusion_include {n m : ℕ} (h : n ≤ m) :
    Inst.CoHom.comp (ExtensionalMLTT.Finite.inclusion.{u} h) (finiteInclusion m) =
      Inst.CoHom.comp (finiteInclusion n) (Finite.inclusion h) := rfl

/-- Semantic consequence is preserved and reflected at every fixed universe count. -/
theorem Embedding.finite_entails_iff (levels : ℕ)
    (H : Set (ExtensionalMLTT.Finite.Sentence levels)) (j : ExtensionalMLTT.Finite.Sentence levels) :
    (ExtensionalMLTT.Finite.room.{u} levels).Entails H j ↔
      (Finite.room.{u} levels).Entails (finiteSentence levels '' H) (finiteSentence levels j) :=
  (finiteInclusion levels).entails_iff (finiteInclusion_modelExpansive levels) (Discrete.mk ()) H j

/-- The hierarchy-level inclusion also preserves and reflects semantic consequence. -/
theorem Embedding.hierarchy_entails_iff (H : Set ExtensionalMLTT.Institution.Sentence.{u})
    (j : ExtensionalMLTT.Institution.Sentence.{u}) :
    ExtensionalMLTT.Institution.room.Entails H j ↔
      Institution.room.Entails (hierarchySentence '' H) (hierarchySentence j) :=
  hierarchyInclusion.entails_iff hierarchyInclusion_modelExpansive (Discrete.mk ()) H j

/-- Set realization through W agrees with the existing base interpretation. -/
@[simp] theorem SetTheoryInterpretation.interpret_base (j : ExtensionalMLTT.Institution.Sentence.{u}) :
    interpret (Embedding.hierarchySentence j) = ExtensionalMLTT.SetTheoryInterpretation.interpret j := by
  cases j
  simp [interpret, Embedding.hierarchySentence, Embedding.judgment,
    ExtensionalMLTT.SetTheoryInterpretation.interpret]

/-- The W realization changes sentences and keeps the hierarchy model. -/
theorem SetTheoryInterpretation.toSetTheory_modelExpansive :
    toSetTheory.{u}.ModelExpansive := by
  intro S T
  exact ⟨T, rfl⟩

/-- Concrete soundness makes W realization a logical-system comorphism. -/
noncomputable def SetTheoryInterpretation.toSetTheoryLogic :
    LogicalSystem.CoHom Institution.logic.{u} ExtensionalMLTT.SetTheoryInterpretation.logic.{u} where
  Φ := toSetTheory.Φ
  ρ := toSetTheory.ρ
  map_derives := by
    intro S H j h T hT
    apply Institution.logic_sound S H j h T
    intro φ hφ
    exact hT _ ⟨φ, hφ, rfl⟩

/-- Semantic entailment can be borrowed through the W realization. -/
theorem SetTheoryInterpretation.entails_iff (H : Set Institution.Sentence.{u})
    (j : Institution.Sentence.{u}) :
    Institution.room.Entails H j ↔
      ExtensionalMLTT.SetTheoryInterpretation.room.Entails (interpret '' H) (interpret j) :=
  toSetTheory.entails_iff toSetTheory_modelExpansive (Discrete.mk ()) H j

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
