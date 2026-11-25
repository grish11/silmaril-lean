module

public import Silmaril.Semantics.Operational.Projection.Defs

public section

namespace Silmaril.Proofs.Semantics.Operational.Projection

open Silmaril.Semantics.Operational

variable {F S A B : Type*} {presented : Cslib.LTS F A} {semantic : Cslib.LTS S B}
  {projectState : F → S} {projectAction : A → B}
  (projection : Projection presented semantic projectState projectAction)

include projection

theorem execution_sound {source target : F} {labels : List A} {states : List F}
    (run : presented.Execution source labels target states) :
    semantic.Execution (projectState source) (labels.map projectAction)
      (projectState target) (states.map projectState) := by
  induction run with
  | refl => exact .refl _
  | stepL edge _ ih => exact .stepL (projection.sound edge) ih

theorem execution_readback {source target : S} {labels : List B} {states : List S}
    (run : semantic.Execution source labels target states) {initial : F}
    (agrees : projectState initial = source) :
    ∃ final actions witnesses, presented.Execution initial actions final witnesses ∧
      actions.map projectAction = labels ∧ witnesses.map projectState = states ∧
      projectState final = target := by
  induction run generalizing initial with
  | refl =>
    exact ⟨initial, [], [initial], .refl initial, rfl, by simp [agrees], agrees⟩
  | stepL step _ ih =>
    obtain ⟨action, next, edge, actionEq, stateEq⟩ := projection.readback (agrees.symm ▸ step)
    obtain ⟨final, actions, witnesses, tail, actionEqs, stateEqs, finalEq⟩ := ih stateEq
    exact ⟨final, action :: actions, initial :: witnesses, .stepL edge tail,
      by simp [actionEq, actionEqs], by simp [agrees, stateEqs], finalEq⟩

end Silmaril.Proofs.Semantics.Operational.Projection
