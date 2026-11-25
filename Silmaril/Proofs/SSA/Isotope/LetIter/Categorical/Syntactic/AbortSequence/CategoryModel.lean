module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Iteration.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Uniformity.Thms

/-! # Model laws of the abort-extended syntactic interpretation -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.ModelProofs

open CategoryTheory CategoryTheory.Limits
open Silmaril.Thesis.LambdaIter.Syn (SynCat)
open Silmaril.Thesis.LambdaIter.Syn.SynCat (ValueCat values IsPureMor)
open Silmaril.Thesis.LambdaIter.LocallyNameless (HasType Pure)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "I" => values S
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe
local notation "Jq" => repairedValues (τ := τ) (Φ := Φ) pe
local notation "cmp" => repairedProjectionCoprodIso pe

private theorem projectedUniformitySquare {A D B : SynCat S}
    (f : A ⟶ B ⨿ A) (g : D ⟶ B ⨿ D) (h : A ⟶ D)
    (comm : ((P).map f ≫ (cmp B A).hom) ≫ coprod.map (𝟙 ((P).obj B)) ((P).map h) =
      (P).map h ≫ ((P).map g ≫ (cmp B D).hom)) :
    (P).map (f ≫ coprod.map (𝟙 B) h) = (P).map (h ≫ g) := by
  have left :
      ((P).map f ≫ (cmp B A).hom) ≫ coprod.map (𝟙 ((P).obj B)) ((P).map h) =
        (P).map (f ≫ coprod.map (𝟙 B) h) ≫ (cmp B D).hom := by
    rw [Category.assoc, ← (P).map_id B, repairedProjection_coprodIso_map,
      ← Category.assoc, ← (P).map_comp]
  rw [left, ← Category.assoc, ← (P).map_comp] at comm
  exact (cancel_mono (cmp B D).hom).mp comm

/-- Pure uniformity transports to the chosen iteration and coproducts of the quotient. -/
theorem quotientUniformity :
    ∀ {A D : ValueCat S} {B : Q}
      (f : (Jq).obj A ⟶ B ⨿ (Jq).obj A) (g : (Jq).obj D ⟶ B ⨿ (Jq).obj D)
      (h : A ⟶ D),
      f ≫ coprod.map (𝟙 B) ((Jq).map h) = (Jq).map h ≫ g →
        CategoryTheory.iterate f = (Jq).map h ≫ CategoryTheory.iterate g := by
  intro A D B f g h comm
  rcases B with ⟨B⟩
  obtain ⟨f, rfl⟩ := repairedIteration_body_surjective pe f
  obtain ⟨g, rfl⟩ := repairedIteration_body_surjective pe g
  have square := projectedUniformitySquare pe f g ((I).map h) comm
  have step := repairedProjection_pure_uniformity pe f g h square
  rw [repairedIteration_map, repairedIteration_map]
  exact step.trans ((P).map_comp _ _)

local instance modelThesisTypeFormers : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance modelThesisHasTy : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ
local instance modelThesisHasEff : Thesis.LambdaIter.HasEff Φ ε := Bridge.thesisHasEff Φ ε

theorem repairedInstructionModel_pure (f : Φ) (hf : IsPure pe f) :
    ∃ p : (typeModel (Φ := Φ) pe).obj (instrSrc f) ⟶
        (typeModel (Φ := Φ) pe).obj (instrTrg f),
      (repairedInstructionModel pe).denote f = (Jq).map p := by
  refine ⟨⟨(instructionModel pe).denote f, ?_⟩, rfl⟩
  change IsPureMor ((instructionModel pe).denote f)
  exact ⟨.op f (.bv 0), HasType.op HasType.newest, Pure.op hf Pure.bv, rfl⟩

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.ModelProofs
