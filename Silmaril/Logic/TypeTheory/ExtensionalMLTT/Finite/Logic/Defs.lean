module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Soundness.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Inclusion
public import Silmaril.Logic.Institution.Metatheory.Entailment

@[expose] public section

/-!
# Actual bounded rules on the existing finite extensional institution

`logic n` adds actual `JEqB n` derivability to the existing bounded sentences,
finite-tower models and satisfaction. It preserves the existing semantic
`room`, `inst`, `bundled`, level inclusions and Hets graph. Arbitrary bounded
judgment hypotheses remain actual rule leaves, including under binders.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory

universe u

/-- The existing finite institution equipped with all actual bounded target rules. -/
def logic (levels : ℕ) : LogicalSystem.{0, 0, 0, u + 1, u + 1} (Discrete Unit) where
  I := inst.{u} levels
  Derives _ H j := ECtx.JEqB levels (Subtype.val '' H) j.val.Γ j.val.A j.val.a j.val.b
  refl _ j := .hyp ⟨j, Set.mem_singleton j, rfl⟩
  mono := by
    intro S H K j hHK h
    exact h.mono (Set.image_mono hHK)
  trans := by
    intro S H Δ j hΔ h
    apply h.bind
    rintro q ⟨k, hk, rfl⟩
    rcases hk with hk | hk
    · exact .hyp ⟨k, hk, rfl⟩
    · exact hΔ k hk
  map_derives := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ σ H j h
    rw [Subsingleton.elim σ (𝟙 _), CategoryTheory.Functor.map_id]
    simpa using h

/-- Each existing finite inclusion also transports all actual bounded derivations. -/
def inclusionLogic {n m : ℕ} (h : n ≤ m) : LogicalSystem.CoHom (logic.{u} n) (logic.{u} m) where
  Φ := (inclusion.{u} h).Φ
  ρ := (inclusion.{u} h).ρ
  map_derives := by
    intro S H j hj
    apply hj.transform h
    rintro q ⟨k, hk, rfl⟩
    exact .hyp ⟨includeSentence h k, ⟨k, hk, rfl⟩, rfl⟩

/-- Compatibility name for the proof-preserving finite inclusion. -/
def inclusionLogical {n m : ℕ} (h : n ≤ m) :
    LogicalSystem.CoHom (logic.{u} n) (logic.{u} m) := inclusionLogic h

/-- Add one available universe without changing any existing rule parameter. -/
def successorLogical (n : ℕ) : LogicalSystem.CoHom (logic.{u} n) (logic.{u} (n + 1)) :=
  inclusionLogical (Nat.le_succ n)

/-- A bounded actual Nat sentence, including at rule budget zero. -/
def zeroSentence (n : ℕ) : Sentence n :=
  ⟨⟨.nil, .nats, .zero, .zero⟩, Nat.zero_le n⟩

/-- A bounded Empty sentence refuted by every actual finite tower. -/
def emptySentence (n : ℕ) : Sentence n :=
  ⟨⟨.nil, .empty, .zero, .zero⟩, Nat.zero_le n⟩

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite
