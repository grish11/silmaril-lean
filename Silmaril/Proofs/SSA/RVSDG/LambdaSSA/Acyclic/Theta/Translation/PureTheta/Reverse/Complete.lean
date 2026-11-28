module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse.Defs

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse.Proofs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A : τ} [DecidableEq τ]

theorem candidate_generated (s : Loop Φ ε A) (pureFirst : Bool) :
    candidate (s.compile pureFirst) = some (s, pureFirst) := by
  unfold candidate read Loop.compile
  rw [NestedTheta.Term.toTerm_toGraph (s.code pureFirst).1]
  cases pureFirst with
  | false =>
    change decode (.ordered (.classifier s.decide), .value s.value.op s.bottom) = some (s, false)
    simp [decode, decodePair, MixedRows.value, MixedRows.instruction, s.value.input, s.value.output,
      s.decide.input, s.decide.output]
  | true =>
    change decode (.value s.value.op s.bottom, .ordered (.classifier s.decide)) = some (s, true)
    simp [decode, decodePair, MixedRows.value, MixedRows.instruction, s.value.input, s.value.output,
      s.decide.input, s.decide.output]

variable [DecidableEq Φ]

theorem recover_generated (s : Loop Φ ε A) (pureFirst : Bool) :
    recover (s.compile pureFirst) = some ⟨s, pureFirst, rfl⟩ := by
  simp [recover, candidate_generated, certify]

theorem recover_isSome_iff (g : Graph Φ ε A) :
    (recover g).isSome = true ↔ ∃ (s : Loop Φ ε A) (pureFirst : Bool), s.compile pureFirst = g := by
  constructor
  · cases recover g with
    | none => simp
    | some f => exact fun _ => ⟨f.loop, f.pureFirst, f.wiring⟩
  · rintro ⟨s, pureFirst, rfl⟩
    simp [recover_generated]

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse.Proofs
