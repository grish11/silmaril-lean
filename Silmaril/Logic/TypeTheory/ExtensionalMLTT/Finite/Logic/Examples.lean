module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Logic.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Derivation.Examples

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite

open CategoryTheory

universe u

/-- A bounded successor sentence, independent of object-language universe levels. -/
def successorZeroSentence (n : ℕ) : Sentence n :=
  ⟨⟨.nil, .nats, .succ .zero, .succ .zero⟩, Nat.zero_le n⟩

/-- An actual hypothesis leaf feeds the target successor rule in the finite logical system. -/
theorem successor_from_hypothesis (n : ℕ) :
    (logic.{u} n).Derives (Discrete.mk ()) {zeroSentence n} (successorZeroSentence n) :=
  .succ (.hyp ⟨zeroSentence n, Set.mem_singleton _, rfl⟩)

/-- Level inclusion transports an actual derivation with its actual mapped hypothesis set. -/
theorem successor_from_included_hypothesis {n m : ℕ} (h : n ≤ m) :
    (logic.{u} m).Derives (Discrete.mk ())
      (includeSentence h '' {zeroSentence n}) (includeSentence h (successorZeroSentence n)) :=
  (inclusionLogic.{u} h).map_derives (Discrete.mk ()) _ _ (successor_from_hypothesis.{u} n)

/-- Actual beta computation inhabits the finite logical system's original bounded syntax. -/
theorem beta_derivable :
    (logic.{u} 1).Derives (Discrete.mk ()) ∅
      ⟨⟨.nil, .nats, .app (.abs .nats (.bv 0)) .zero, .zero⟩, Nat.zero_le 1⟩ := by
  change ECtx.JEqB 1 (Subtype.val '' (∅ : Set (Sentence 1))) .nil .nats
    (.app (.abs .nats (.bv 0)) .zero) .zero
  rw [Set.image_empty]
  exact bounded_identity_beta

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite
