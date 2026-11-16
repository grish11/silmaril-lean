module

public import Silmaril.Proofs.Logic.Reachability.RuleSystem.Soundness

@[expose] public section
namespace Silmaril.Logic.Reachability.RuleSystem

/-- Stored transitions must be identified with the rule-induced relation.
Claim captures parameterize certificates and never identify rule valuations. -/
theorem sentence_sound {S : Type} {cfg : S} {A : Signature cfg} (M : Model cfg A)
    {ι : Type} (rules : ι → Scheme (M.carrier cfg))
    (wellDefined : WeaklyWellDefined rules)
    (step_eq : step cfg M = Induced rules) (p : Sentence cfg A)
    (mode : p.mode = .allPath) (n : Nat)
    (cert : ∀ a : (i : Fin p.variableCount) → M.carrier (p.context i),
      Certificate rules (fun w => w ∈ M.denote a p.post) n)
    (entry : ∀ a w, w ∈ M.denote a p.pre →
      w ∈ M.denote a p.post ∨ ∃ j, (cert a).node j w) : p.Satisfies cfg M := by
  intro a w hw
  rw [mode]
  rw [step_eq]
  exact (cert a).sound wellDefined (entry a w hw)

theorem compiled_matching_sound {S : Type} {cfg : S} {A : Signature cfg}
    (M : Model cfg A) {ι : Type} (rules : ι → Scheme (M.carrier cfg))
    (wellDefined : WeaklyWellDefined rules)
    (step_eq : step cfg M = Induced rules) (p : Sentence cfg A)
    (mode : p.mode = .allPath) (n : Nat)
    (cert : ∀ a : (i : Fin p.variableCount) → M.carrier (p.context i),
      Certificate rules (fun w => w ∈ M.denote a p.post) n)
    (entry : ∀ a w, w ∈ M.denote a p.pre →
      w ∈ M.denote a p.post ∨ ∃ j, (cert a).node j w) :
    Matching.FixedPoint.Sentence.Satisfies M (encode cfg p) :=
  (encode_correct M p).2
    (sentence_sound M rules wellDefined step_eq p mode n cert entry)

end Silmaril.Logic.Reachability.RuleSystem
