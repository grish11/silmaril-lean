module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Reverse.Defs

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Reverse.Proofs

open PureRow (Segment)
open MixedRows (Row)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A P B C : τ}

private def labels (s : Segment Φ ε A P B C) (pureFirst : Bool) : List (Row τ Φ ε) :=
  let value := Row.value s.value.op s.bottom
  let first := Row.ordered (ε := ε) (.call s.first)
  let last := Row.ordered (ε := ε) (.call s.second)
  if pureFirst then [value, first, last] else [first, value, last]

private theorem read_generated (s : Branch Φ ε A P B C) (pureFirst : Bool) :
    read (s.compile pureFirst) = some (labels s.left pureFirst, labels s.right true) := by
  unfold read Branch.compile
  rw [NestedTheta.Term.toTerm_toGraph (s.code pureFirst).1]
  cases pureFirst <;> rfl

variable [DecidableEq τ]

private theorem decodeSegment_generated (s : Segment Φ ε A P B C) :
    decodeSegment (.value s.value.op s.bottom) (.ordered (.call s.first)) (.ordered (.call s.second)) =
      some ⟨B, s⟩ := by
  simp [decodeSegment, MixedRows.value, MixedRows.instruction, s.value.input, s.value.output,
    s.first.input, s.first.output, s.second.input, s.second.output]

theorem candidate_generated (s : Branch Φ ε A P B C) (pureFirst : Bool) :
    candidate (s.compile pureFirst) = some ⟨B, s, pureFirst⟩ := by
  unfold candidate
  rw [read_generated]
  cases pureFirst <;> cases s with
  | mk l r => simp [decode, decodeLeft, decodeRight, labels, decodeSegment_generated l, decodeSegment_generated r]

variable [DecidableEq Φ]

theorem recover_generated (s : Branch Φ ε A P B C) (pureFirst : Bool) :
    recover (s.compile pureFirst) = some ⟨B, s, pureFirst, rfl⟩ := by
  simp [recover, candidate_generated, certify]

theorem recover_isSome_iff (g : Graph Φ ε A P C) :
    (recover g).isSome = true ↔ ∃ (B : τ) (s : Branch Φ ε A P B C) (pureFirst : Bool), s.compile pureFirst = g := by
  constructor
  · cases recover g with
    | none => simp
    | some f => exact fun _ => ⟨f.middle, f.branch, f.pureFirst, f.wiring⟩
  · rintro ⟨B, s, pureFirst, rfl⟩
    simp [recover_generated]

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Reverse.Proofs
