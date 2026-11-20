module

public import Silmaril.Compiler.Explorer.Text.Defs
import Silmaril.Proofs.Compiler.Explorer.Text

/-!
# Text-file problems: theorems

* `Stage.validated_comp`: validated stages compose (through any intermediate relation, into the
  relational composite).
* `Verdict.not_both`: a statement is not both proved and refuted.
* `Reading.toRel_of`: a reading's relation from the parses and the refinement.
-/

@[expose] public section

namespace Silmaril.Compiler.Explorer

/-- **Validated stages compose.** -/
theorem Stage.validated_comp {α β γ : Type} {f : Stage α β} {g : Stage β γ} {R : α → β → Prop}
    {S : β → γ → Prop} (hf : f.validated R) (hg : g.validated S) :
    (f.comp g).validated (fun a c => ∃ b, R a b ∧ S b c) := Proofs.Stage.validated_comp hf hg

/-- Strengthening a relation does not require any change to either parser. -/
theorem Stage.pullback_refines {α β σ τ : Type} (source : Stage α σ) (target : Stage β τ)
    {R S : σ → τ → Prop} (refines : RelProblem.Refines R S) :
    RelProblem.Refines (source.pullback target R) (source.pullback target S) :=
  fun _ _ ⟨s, t, hs, ht, related⟩ => ⟨s, t, hs, ht, refines s t related⟩

theorem RelProblem.Refines.refl {α β : Type} (R : α → β → Prop) : RelProblem.Refines R R :=
  fun _ _ related => related

theorem RelProblem.Refines.trans {α β : Type} {R S T : α → β → Prop}
    (first : RelProblem.Refines R S) (next : RelProblem.Refines S T) : RelProblem.Refines R T :=
  fun a b related => next a b (first a b related)

/-- A morphism transports evidence at the chosen pair; refutations pull back. -/
theorem RelProblem.Morphism.sound {α β σ τ : Type} {P : RelProblem α β} {Q : RelProblem σ τ}
    (m : P.Morphism Q) (related : P.Statement) : Q.Statement := by
  simpa only [RelProblem.Statement, m.onSource, m.onTarget] using m.preserves _ _ related

theorem RelProblem.Morphism.identity_comp {α β σ τ : Type} {P : RelProblem α β} {Q : RelProblem σ τ}
    (m : P.Morphism Q) : (Morphism.identity P).comp m = m := rfl

theorem RelProblem.Morphism.comp_identity {α β σ τ : Type} {P : RelProblem α β} {Q : RelProblem σ τ}
    (m : P.Morphism Q) : m.comp (Morphism.identity Q) = m := rfl

theorem RelProblem.Morphism.comp_assoc {α β σ τ γ δ μ ν : Type}
    {P : RelProblem α β} {Q : RelProblem σ τ} {R : RelProblem γ δ} {S : RelProblem μ ν}
    (m₁ : P.Morphism Q) (m₂ : Q.Morphism R) (m₃ : R.Morphism S) :
    (m₁.comp m₂).comp m₃ = m₁.comp (m₂.comp m₃) := rfl

/-- A statement is not both proved and refuted. -/
theorem Verdict.not_both {p : Prop} (h : p) (n : ¬ p) : False := n h

/-- **A reading's relation** from the two parses and the refinement of their problem. -/
theorem Reading.toRel_of {α β σ τ R T : Type} (r : Reading α β σ τ R T) {a : α} {b : β} {s : σ}
    {t : τ} (hs : r.parseSource.run a = .ok s) (ht : r.parseTarget.run b = .ok t)
    (h : (r.problem s t).Refines) : r.toRel a b := ⟨s, t, hs, ht, h⟩

end Silmaril.Compiler.Explorer

end
