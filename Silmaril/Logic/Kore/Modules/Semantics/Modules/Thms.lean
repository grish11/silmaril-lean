module

public import Silmaril.Logic.Kore.Modules.Semantics.Modules.Defs

@[expose] public section
namespace Silmaril.Logic.Kore.Modules.Semantics
open Checking
variable {ambient : Scope}

/-- Each actual retained source declaration has the compiled sentence's truth
value, through independent raw semantics, not just a checker equation. -/
theorem checkedSentence_sound (d : CheckedSentence ambient)
    (M : Matching.FirstOrder.Model ambient.signature) :
    Satisfies M d.fuel d.raw ↔ FirstOrder.Sentence.Satisfies M d.sentence :=
  sentence_sound M d.fuel d.raw d.sentence d.elaborated

theorem models_sound (m : CheckedModule ambient)
    (M : Matching.FirstOrder.Model ambient.signature) :
    Models m M ↔ ∀ p ∈ m.axiomSet, FirstOrder.Sentence.Satisfies M p := by
  constructor
  · intro sourceModel p hp
    rcases hp with ⟨d, hd, rfl⟩
    exact (checkedSentence_sound d M).1 (sourceModel d hd)
  · intro typedModel d hd
    exact (checkedSentence_sound d M).2 (typedModel d.sentence ⟨d, hd, rfl⟩)

/-- Raw source consequence and the existing actual module presentation judgment
coincide, with exactly the same models and all transitively imported axioms. -/
theorem proves_sound (m : CheckedModule ambient) (claim : CheckedSentence ambient) :
    Proves m claim ↔ m.Proves claim.sentence := by
  constructor
  · intro sourceProof M typedModel
    exact (checkedSentence_sound claim M).1 (sourceProof M ((models_sound m M).2 typedModel))
  · intro typedProof M sourceModel
    exact (checkedSentence_sound claim M).2 (typedProof M ((models_sound m M).1 sourceModel))

/-- Imported source consequence is preserved using the already proved genuine
module presentation arrow; no additional model axiom or alias assumption. -/
theorem proves_import (parent child : CheckedModule ambient)
    (h : parent.asImport ∈ child.imports) (claim : CheckedSentence ambient)
    (proof : Proves parent claim) : Proves child claim :=
  (proves_sound child claim).2
    (CheckedModule.proves_import parent child h claim.sentence ((proves_sound parent claim).1 proof))
end Silmaril.Logic.Kore.Modules.Semantics
