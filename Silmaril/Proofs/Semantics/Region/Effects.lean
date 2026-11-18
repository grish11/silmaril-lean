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

theorem outcome_covered_bound [CompleteLattice E] {A : S → Prop}
    {observe : Sum Ev Stop → E} {bound : E}
    (step : ∀ s es t, U (T.pc s) → T.step s es t → ∀ e ∈ es, observe (.inl e) ≤ bound)
    (halt : ∀ t k, U (T.pc t) → T.halt t k → observe (.inr k) ≤ bound) :
    outcomeEnvelope T A U observe ≤ bound := by
  apply iSup_le; intro o
  apply iSup_le; intro ho
  cases o with
  | inl e => exact covered_bound step e ho
  | inr k =>
    obtain ⟨s, es, t, _, path, stopped⟩ := ho
    exact halt t k (inside_end path) stopped

theorem useDef_sequence_assoc {R : Type*} (a b c : UseDef R) :
    (a.sequence b).sequence c = a.sequence (b.sequence c) := by
  cases a; cases b; cases c
  simp only [UseDef.sequence]
  congr 1 <;> ext r <;> simp only [Set.mem_union, Set.mem_sdiff] <;> tauto

theorem useDef_sequence_mono {R : Type*} {a b c d : UseDef R}
    (ha : a.uses ⊆ b.uses ∧ b.definiteDefs ⊆ a.definiteDefs)
    (hc : c.uses ⊆ d.uses ∧ d.definiteDefs ⊆ c.definiteDefs) :
    (a.sequence c).uses ⊆ (b.sequence d).uses ∧
      (b.sequence d).definiteDefs ⊆ (a.sequence c).definiteDefs := by
  constructor
  · rintro r (h | ⟨h, hn⟩)
    · exact Or.inl (ha.1 h)
    · exact Or.inr ⟨hc.1 h, fun h => hn (ha.2 h)⟩
  · rintro r (h | h)
    · exact Or.inl (ha.2 h)
    · exact Or.inr (hc.2 h)

theorem useDef_selection_lub {R : Type*} (a b c : UseDef R) :
    ((a.selection b).uses ⊆ c.uses ∧ c.definiteDefs ⊆ (a.selection b).definiteDefs) ↔
      (a.uses ⊆ c.uses ∧ c.definiteDefs ⊆ a.definiteDefs) ∧
      (b.uses ⊆ c.uses ∧ c.definiteDefs ⊆ b.definiteDefs) := by
  simp only [UseDef.selection, Set.union_subset_iff, Set.subset_inter_iff]
  tauto

theorem prepend_assoc {sig : BlockSignature} (a b c : InstructionSummary sig) :
    (a.prepend b).prepend c = a.prepend (b.prepend c) := by
  cases a; cases b; cases c
  simp only [InstructionSummary.prepend, Set.union_assoc, useDef_sequence_assoc]

theorem effects_direct {I : Type*} {sig : BlockSignature}
    (analyze : I → InstructionSummary sig) (b : Block I) (e : Atom sig.Payload) :
    e ∈ (b.effects analyze).direct ↔
      ∃ i ∈ b.body ++ [b.final], e ∈ (analyze i).direct := by
  rcases b with ⟨body, final⟩
  induction body with
  | nil => simp [Block.effects]
  | cons i rest ih =>
    simp only [Block.effects, List.foldr_cons, InstructionSummary.prepend] at *
    simp only [Set.mem_union, List.cons_append, List.mem_cons, exists_eq_or_imp]
    exact or_congr Iff.rfl ih

theorem effects_control {I : Type*} {sig : BlockSignature}
    (analyze : I → InstructionSummary sig) (b : Block I) :
    (b.effects analyze).control = (analyze b.final).control := by
  rcases b with ⟨body, final⟩
  induction body with
  | nil => rfl
  | cons i rest ih => exact ih

/-- Terminal control summaries need coverage of halts as well as normal exits.
This prevents a body fault from disappearing from the block's effects. -/
theorem control_bound_of_terminal {Term : Type*} {T : TransitionSystem S L Ev Stop}
    {A : S → Prop} {U : L → Prop} {term : Term} {transfer : Term → S → Prop}
    {bound : Set (ControlOutcome L Stop)}
    (normalCoverage : TerminatorCoverage T A U term transfer)
    (normal : ∀ t, transfer term t → .next (T.pc t) ∈ bound)
    (haltCoverage : ∀ s es t k, A s → Inside T U s es t → T.halt t k → transfer term t)
    (halt : ∀ t k, transfer term t → T.halt t k → .halt k ∈ bound) :
    ControlBound T A U bound := by
  constructor
  · intro s es t admitted path
    exact normal t (normalCoverage s es t admitted path)
  · intro s es t k admitted path stopped
    exact halt t k (haltCoverage s es t k admitted path stopped) stopped

end Silmaril.Semantics.Region.Effects.Proofs
