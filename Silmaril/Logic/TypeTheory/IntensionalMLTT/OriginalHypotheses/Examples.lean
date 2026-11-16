module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses.Examples

/-- A scoped body assumption whose leaf is actually underneath a lambda binder. -/
def bodySentence : ScopedTyping := ⟨1, Context.nil.snoc .nat, .var 0, .nat⟩

def naturalIdentity : Term 0 := .lam .nat (.var 0)

def bodyOriginal : Derivation (Context.nil.snoc .nat) (.var 0) .nat :=
  .var (.snoc .nil (.nat .nil)) .here

/-- The proof genuinely uses a hypothesis leaf as its lambda body. -/
def underBinder : DerivationH {bodySentence} .nil naturalIdentity (.pi .nat .nat) :=
  .lam (.nat .nil) (.nat (.snoc .nil (.nat .nil))) (.hyp rfl)

/-- This is a computed whole-proof bound, including both formation premises. -/
theorem underBinder_budget : underBinder.universeBudget = 1 := rfl

/-- Substitution replaces that actual nested leaf with the supplied original proof data. -/
noncomputable def substituted : DerivationH ∅ .nil naturalIdentity (.pi .nat .nat) :=
  underBinder.bind (by
    intro q hq
    have hq' : q = bodySentence := hq
    subst q
    exact .ofOriginal bodyOriginal)

theorem substituted_original : Typing .nil naturalIdentity (.pi .nat .nat) :=
  ⟨substituted.erase⟩

/-- The body replacement itself fits the same finite universe count. -/
noncomputable def bodyReplacement :
    BoundedDerivationH 1 ∅ (Context.nil.snoc .nat) (.var 0) .nat :=
  .ofOriginal ⟨bodyOriginal, by decide⟩

/-- Bounded substitution reaches an actual original proof at that unchanged whole-tree cap. -/
noncomputable def substitutedBounded : BoundedDerivation 1 .nil naturalIdentity (.pi .nat .nat) :=
  (show BoundedDerivationH 1 {bodySentence} .nil naturalIdentity (.pi .nat .nat) from
    ⟨underBinder, by decide⟩).bind (by
      intro q hq
      have hq' : q = bodySentence := hq
      subst q
      exact bodyReplacement) |>.toOriginal

/-- The actual body assumption is realizable, hence so is the hypothetical lambda proof. -/
theorem underBinder_realizes : RawRealizability.Valid .nil naturalIdentity (.pi .nat .nat) := by
  apply underBinder.realizes
  intro q hq
  have hq' : q = bodySentence := hq
  subst q
  exact bodyOriginal.realizes

/-- Original zero really is captured by a zero-budget proof, with no stage-one strengthening. -/
noncomputable def zeroAtZero : BoundedDerivationH 0 ∅ .nil .zero .nat :=
  .ofOriginal ⟨.zero .nil, by decide⟩

/-- Empty hypotheses cannot create a new original Empty inhabitant. -/
theorem no_original_empty (t : Term 0) : ¬ Nonempty (DerivationH ∅ .nil t .empty) := by
  intro h
  exact RawRealizability.no_closed_empty t (DerivationH.empty_iff.mp h)

end Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses.Examples
