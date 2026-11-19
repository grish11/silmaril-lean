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

theorem outcomeEnvelope_le_iff [CompleteLattice E] (T : TransitionSystem S L Ev Stop)
    (A : S → Prop) (U : L → Prop) (observe : Sum Ev Stop → E) (bound : E) :
    outcomeEnvelope T A U observe ≤ bound ↔
      ∀ o, MayObservation T A U o → observe o ≤ bound := by
  simp only [outcomeEnvelope, iSup_le_iff]

/-- Step coverage plus halt coverage, without a BB partition or termination
assumption, bounds every direct event and every reachable distinguished halt. -/
theorem outcome_covered_bound [CompleteLattice E] {T : TransitionSystem S L Ev Stop}
    {A : S → Prop} {U : L → Prop} {observe : Sum Ev Stop → E} {bound : E}
    (step : ∀ s es t, U (T.pc s) → T.step s es t → ∀ e ∈ es, observe (.inl e) ≤ bound)
    (halt : ∀ t k, U (T.pc t) → T.halt t k → observe (.inr k) ≤ bound) :
    outcomeEnvelope T A U observe ≤ bound := Proofs.outcome_covered_bound step halt

theorem atKind_union {K : Type*} {P : K → Type*} (a b : Set (Atom P)) (k : K) :
    atKind (a ∪ b) k = atKind a k ∪ atKind b k := rfl

theorem atKind_iUnion {K J : Type*} {P : K → Type*} (sets : J → Set (Atom P)) (k : K) :
    atKind (⋃ j, sets j) k = ⋃ j, atKind (sets j) k := by
  ext x; simp only [atKind, Set.mem_ofPred_eq, Set.mem_iUnion]

/-- Relabeling observations preserves arbitrary may-effect joins (unions).
It need not preserve intersections when categories or payloads are identified. -/
theorem Renaming.map_iUnion {K H J : Type*} {P : K → Type*} {Q : H → Type*}
    (f : Renaming P Q) (sets : J → Set (Atom P)) :
    f.map (⋃ j, sets j) = ⋃ j, f.map (sets j) := Set.image_iUnion

theorem Renaming.map_id {K : Type*} {P : K → Type*} (effects : Set (Atom P)) :
    (Renaming.id P).map effects = effects := by
  change (fun a : Atom P => ⟨a.1, a.2⟩) '' effects = effects
  exact Set.image_id effects

theorem Renaming.map_then {K H J : Type*}
    {P : K → Type*} {Q : H → Type*} {R : J → Type*}
    (f : Renaming P Q) (g : Renaming Q R) (effects : Set (Atom P)) :
    (f.then g).map effects = g.map (f.map effects) := by
  simp only [Renaming.map, Set.image_image, Renaming.atom, Renaming.then, Function.comp_apply]
  rfl

theorem Renaming.map_mono {K H : Type*} {P : K → Type*} {Q : H → Type*}
    (f : Renaming P Q) {a b : Set (Atom P)} (h : a ⊆ b) : f.map a ⊆ f.map b :=
  Set.image_mono h

/-- Soundness transports along a monotone observation map, even if it forgets
information. Reflection and exactness would require additional hypotheses. -/
theorem bound_transport {F : Type*} [Preorder E] [Preorder F]
    {T : TransitionSystem S L Ev Stop} {A : S → Prop} {U : L → Prop}
    {observe : Ev → E} {bound : E} (f : E → F) (mono : Monotone f)
    (sound : SoundBound T A U observe bound) :
    SoundBound T A U (f ∘ observe) (f bound) := fun e he => mono (sound e he)

theorem UseDef.sequence_assoc {R : Type*} (a b c : UseDef R) :
    (a.sequence b).sequence c = a.sequence (b.sequence c) := Proofs.useDef_sequence_assoc a b c

theorem UseDef.sequence_mono {R : Type*} {a b c d : UseDef R}
    (ha : a.uses ⊆ b.uses ∧ b.definiteDefs ⊆ a.definiteDefs)
    (hc : c.uses ⊆ d.uses ∧ d.definiteDefs ⊆ c.definiteDefs) :
    (a.sequence c).uses ⊆ (b.sequence d).uses ∧
      (b.sequence d).definiteDefs ⊆ (a.sequence c).definiteDefs := Proofs.useDef_sequence_mono ha hc

/-- May uses order covariantly; definite definitions order contravariantly.
Selection is the least upper allowance in this precision order. -/
theorem UseDef.selection_lub {R : Type*} (a b c : UseDef R) :
    ((a.selection b).uses ⊆ c.uses ∧ c.definiteDefs ⊆ (a.selection b).definiteDefs) ↔
      (a.uses ⊆ c.uses ∧ c.definiteDefs ⊆ a.definiteDefs) ∧
      (b.uses ⊆ c.uses ∧ c.definiteDefs ⊆ b.definiteDefs) := Proofs.useDef_selection_lub a b c

theorem InstructionSummary.prepend_assoc {sig : BlockSignature} (a b c : InstructionSummary sig) :
    (a.prepend b).prepend c = a.prepend (b.prepend c) := Proofs.prepend_assoc a b c

theorem Block.effects_direct {I : Type*} {sig : BlockSignature}
    (analyze : I → InstructionSummary sig) (b : Block I) (e : Atom sig.Payload) :
    e ∈ (b.effects analyze).direct ↔
      ∃ i ∈ b.body ++ [b.final], e ∈ (analyze i).direct := Proofs.effects_direct analyze b e

/-- Relates the computed direct union to actual events only with instruction
lookup coverage and a per-step observation theorem. It infers no execution or
interference assumptions from syntax. -/
theorem Block.direct_bound {I : Type*} {sig : BlockSignature}
    {T : TransitionSystem S L Ev Stop} {A : S → Prop} {U : L → Prop}
    (analyze : I → InstructionSummary sig) (b : Block I) (atInstruction : S → I)
    (observe : Ev → Atom sig.Payload)
    (coverage : ∀ s, U (T.pc s) → atInstruction s ∈ b.body ++ [b.final])
    (step : ∀ s es t, U (T.pc s) → T.step s es t →
      ∀ e ∈ es, observe e ∈ (analyze (atInstruction s)).direct) :
    SoundBound T A U (fun e => ({observe e} : Set _)) (b.effects analyze).direct :=
  covered_bound fun s es t hu edge e he => Set.singleton_subset_iff.mpr
    ((Block.effects_direct analyze b _).mpr ⟨atInstruction s, coverage s hu, step s es t hu edge e he⟩)

theorem Block.effects_control {I : Type*} {sig : BlockSignature}
    (analyze : I → InstructionSummary sig) (b : Block I) :
    (b.effects analyze).control = (analyze b.final).control := Proofs.effects_control analyze b

theorem CertifiedBlock.control_sound {I : Type*} {sig : BlockSignature} {c : BlockContract I sig}
    (b : CertifiedBlock c) : c.controlSound b.block.final b.effects.control := by
  simpa only [CertifiedBlock.effects, Block.effects_control] using b.control

/-- Terminator-only control inference requires coverage of normal AND abnormal
escapes. A fault in an earlier instruction cannot silently disappear. -/
theorem control_bound_of_terminal {Term : Type*} {T : TransitionSystem S L Ev Stop}
    {A : S → Prop} {U : L → Prop} {term : Term} {transfer : Term → S → Prop}
    {bound : Set (ControlOutcome L Stop)}
    (normalCoverage : TerminatorCoverage T A U term transfer)
    (normal : ∀ t, transfer term t → .next (T.pc t) ∈ bound)
    (haltCoverage : ∀ s es t k, A s → Inside T U s es t → T.halt t k → transfer term t)
    (halt : ∀ t k, transfer term t → T.halt t k → .halt k ∈ bound) :
    ControlBound T A U bound :=
  Proofs.control_bound_of_terminal normalCoverage normal haltCoverage halt

end Silmaril.Semantics.Region.Effects
