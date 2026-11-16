module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Institution.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Soundness

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

theorem logic_sound : Institution.logic.{u}.Sound := by
  rintro ⟨⟨⟩⟩ H j h T hT
  apply ECtx.JEqH.sound (Discrete.as T) (H := ULift.down '' H) _ h
  rintro q ⟨φ, hφ, rfl⟩
  exact hT φ hφ

theorem setLogic_sound : SetTheoryInterpretation.logic.{u}.Sound :=
  fun _ _ _ h => h

theorem toSetTheory_modelExpansive :
    SetTheoryInterpretation.toSetTheory.{u}.ModelExpansive := by
  intro _ T
  exact ⟨T, rfl⟩

/-- The all-rule soundness theorem supplies the derivability part of realization. -/
@[expose] noncomputable def toSetTheoryLogic :
    LogicalSystem.CoHom Institution.logic.{u} SetTheoryInterpretation.logic.{u} where
  Φ := SetTheoryInterpretation.toSetTheory.Φ
  ρ := SetTheoryInterpretation.toSetTheory.ρ
  map_derives := by
    intro S H j h T hT
    apply logic_sound S H j h T
    intro φ hφ
    exact hT _ ⟨φ, hφ, rfl⟩

theorem toSetTheoryLogic_modelExpansive : toSetTheoryLogic.{u}.ModelExpansive :=
  toSetTheory_modelExpansive

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT
