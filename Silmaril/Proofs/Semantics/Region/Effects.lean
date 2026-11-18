module

public import Silmaril.Semantics.Region.Effects.Defs

@[expose] public section
namespace Silmaril.Semantics.Region.Effects.Proofs
universe u v w x y
variable {S : Type u} {L : Type v} {Ev : Type w} {Stop : Type x} {E : Type y}
variable {T : TransitionSystem S L Ev Stop} {U : L → Prop}

theorem inside_end {s t : S} {es : List Ev} (path : Inside T U s es t) : U (T.pc t) := by
  induction path with
  | refl h => exact h
  | step _ _ _ ih => exact ih

theorem inside_bound [Preorder E] {observe : Ev → E} {bound : E}
    (step : ∀ s es t, U (T.pc s) → T.step s es t → ∀ e ∈ es, observe e ≤ bound)
    {s t : S} {es : List Ev} (path : Inside T U s es t) : ∀ e ∈ es, observe e ≤ bound := by
  induction path with
  | refl => simp
  | step inside edge tail ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact step _ _ _ inside edge e he
    · exact ih e he

theorem covered_bound [CompleteLattice E] {A : S → Prop} {observe : Ev → E} {bound : E}
    (step : ∀ s es t, U (T.pc s) → T.step s es t → ∀ e ∈ es, observe e ≤ bound) :
    SoundBound T A U observe bound := by
  rintro e ⟨s, es, t, tail, f, _, path, edge, member⟩
  have inside : U (T.pc t) := inside_end path
  rcases List.mem_append.mp member with member | member
  · exact inside_bound step path e member
  · exact step t tail f inside edge e member

end Silmaril.Semantics.Region.Effects.Proofs
