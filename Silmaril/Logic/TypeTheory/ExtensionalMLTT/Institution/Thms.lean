module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Institution.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Institution

@[expose] public section

/-! # Sound MLTT logic and its semantic set interpretation -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory

universe u

/-- Every derivation from judgment hypotheses is valid in each hierarchy model. -/
theorem Institution.logic_sound : Institution.logic.{u}.Sound :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.logic_sound

/-- Semantic set consequence is sound by its definition. -/
theorem SetTheoryInterpretation.logic_sound : SetTheoryInterpretation.logic.{u}.Sound :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.setLogic_sound

/-- Every source hierarchy has an expansion along the semantic realization. -/
theorem SetTheoryInterpretation.toSetTheory_modelExpansive :
    SetTheoryInterpretation.toSetTheory.{u}.ModelExpansive :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.toSetTheory_modelExpansive

/-- Soundness makes realization a comorphism of logics as well as institutions. -/
noncomputable def SetTheoryInterpretation.toSetTheoryLogic :
    LogicalSystem.CoHom Institution.logic.{u} SetTheoryInterpretation.logic.{u} :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.toSetTheoryLogic

theorem SetTheoryInterpretation.toSetTheoryLogic_modelExpansive :
    SetTheoryInterpretation.toSetTheoryLogic.{u}.ModelExpansive :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.toSetTheoryLogic_modelExpansive

/-- Semantic entailment can be checked on the translated set constraints. -/
theorem SetTheoryInterpretation.entails_iff (H : Set Institution.Sentence.{u})
    (j : Institution.Sentence.{u}) :
    Institution.room.Entails H j ↔
      SetTheoryInterpretation.room.Entails
        (SetTheoryInterpretation.interpret '' H) (SetTheoryInterpretation.interpret j) :=
  SetTheoryInterpretation.toSetTheory.entails_iff
    SetTheoryInterpretation.toSetTheory_modelExpansive (Discrete.mk ()) H j

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
