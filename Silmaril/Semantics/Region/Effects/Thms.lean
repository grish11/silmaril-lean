module

public import Silmaril.Semantics.Region.Effects.Defs
import Silmaril.Proofs.Semantics.Region.Effects

@[expose] public section
namespace Silmaril.Semantics.Region.Effects
universe u v w x y
variable {S : Type u} {L : Type v} {Ev : Type w} {Stop : Type x} {E : Type y}

/-- The envelope is the least sound allowance, rather than the greatest set
of sound region judgments or a must-effect result. -/
theorem envelope_le_iff [CompleteLattice E] (T : TransitionSystem S L Ev Stop)
    (A : S → Prop) (U : L → Prop) (observe : Ev → E) (bound : E) :
    envelope T A U observe ≤ bound ↔ SoundBound T A U observe bound := by
  simp only [envelope, iSup_le_iff, SoundBound]

theorem envelope_sound [CompleteLattice E] (T : TransitionSystem S L Ev Stop)
    (A : S → Prop) (U : L → Prop) (observe : Ev → E) :
    SoundBound T A U observe (envelope T A U observe) :=
  (envelope_le_iff T A U observe _).mp le_rfl

theorem top_sound [CompleteLattice E] (T : TransitionSystem S L Ev Stop)
    (A : S → Prop) (U : L → Prop) (observe : Ev → E) : SoundBound T A U observe ⊤ :=
  fun _ _ => le_top

/-- A must occurrence implies a possible effect only when the selected
nonempty trace family is covered by the operational observation. -/
theorem must_implies_may {T : TransitionSystem S L Ev Stop} {A : S → Prop} {U : L → Prop}
    {runs : List Ev → Prop} {e : Ev} (must : MustOccur runs e)
    (coverage : ∀ es, runs es → ∀ event ∈ es, MayEffect T A U event) : MayEffect T A U e :=
  let ⟨es, hr⟩ := must.1; coverage es hr e (must.2 es hr)

/-- Coverage of actual steps lifts any local observation bound to regions;
the region need not be partitioned into locally certified basic blocks. -/
theorem covered_bound [CompleteLattice E] {T : TransitionSystem S L Ev Stop}
    {A : S → Prop} {U : L → Prop} {observe : Ev → E} {bound : E}
    (step : ∀ s es t, U (T.pc s) → T.step s es t → ∀ e ∈ es, observe e ≤ bound) :
    SoundBound T A U observe bound := Proofs.covered_bound step

/-- The region bound can be a join of per-label allowances, including Top. -/
theorem labels_bound [CompleteLattice E] {T : TransitionSystem S L Ev Stop}
    {A : S → Prop} {U : L → Prop} {observe : Ev → E} (summary : L → E)
    (step : ∀ s es t, U (T.pc s) → T.step s es t → ∀ e ∈ es, observe e ≤ summary (T.pc s)) :
    SoundBound T A U observe (⨆ l, ⨆ (_ : U l), summary l) :=
  covered_bound (fun s es t hu edge e he =>
    (step s es t hu edge e he).trans (le_iSup_of_le (T.pc s) (le_iSup_of_le hu le_rfl)))

/-- A definition before a use removes an upward-exposed use. Set union of
instruction summaries would incorrectly keep it. -/
theorem sequence_is_not_union :
    (UseDef.sequence (⟨∅, {()}⟩ : UseDef Unit) ⟨{()}, ∅⟩).uses = ∅ ∧
      (({()} : Set Unit) ∪ ∅) ≠ ∅ := by simp [UseDef.sequence]

end Silmaril.Semantics.Region.Effects
