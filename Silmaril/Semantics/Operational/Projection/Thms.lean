module

public import Silmaril.Semantics.Operational.Projection.Defs
import Silmaril.Proofs.Semantics.Operational.Projection

public section

namespace Silmaril.Semantics.Operational.Projection

variable {F S A B : Type*} {presented : Cslib.LTS F A} {semantic : Cslib.LTS S B}
  {projectState : F → S} {projectAction : A → B}
  (projection : Projection presented semantic projectState projectAction)

include projection

theorem step_iff (source : F) (action : B) (target : S) :
    semantic.Tr (projectState source) action target ↔
      ∃ label next, presented.Tr source label next ∧
        projectAction label = action ∧ projectState next = target :=
  ⟨fun step => projection.readback step,
    fun ⟨_, _, step, labelEq, stateEq⟩ => labelEq ▸ stateEq ▸ projection.sound step⟩

theorem execution_sound {source target : F} {labels : List A} {states : List F}
    (run : presented.Execution source labels target states) :
    semantic.Execution (projectState source) (labels.map projectAction)
      (projectState target) (states.map projectState) :=
  Proofs.Semantics.Operational.Projection.execution_sound projection run

/-- Lift a finite execution from the given initial witness. Both complete
lists project exactly, including every action and intermediate state. -/
theorem execution_readback {source target : S} {labels : List B} {states : List S}
    (run : semantic.Execution source labels target states) {initial : F}
    (agrees : projectState initial = source) :
    ∃ final actions witnesses, presented.Execution initial actions final witnesses ∧
      actions.map projectAction = labels ∧ witnesses.map projectState = states ∧
      projectState final = target :=
  Proofs.Semantics.Operational.Projection.execution_readback projection run agrees

end Silmaril.Semantics.Operational.Projection
