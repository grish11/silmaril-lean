module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Derivation
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Inclusion
public import Silmaril.Logic.Institution.Metatheory.Entailment

@[expose] public section

/-!
# Logical systems on the finite MLTT institution tower

The institution's sentences remain syntactically bounded judgments. Its
proof-theoretic consequence relation uses a common bound on every inference
rule, including all members of cofinite premise families. The existing
institution inclusions also preserve this derivability relation.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory

universe u

/-- Extensional MLTT with all inference-rule universes below the fixed count. -/
def logic (levels : ℕ) : LogicalSystem.{0, 0, 0, u + 1, u + 1} (Discrete Unit) where
  I := inst.{u} levels
  Derives _ H j := Ctx.JEqB levels (Subtype.val '' H) j.val.Γ j.val.A j.val.a j.val.b
  refl _ j := .hyp ⟨j, Set.mem_singleton j, rfl⟩
  mono := by
    intro S H H' j hsub h
    exact h.mono (Set.image_mono hsub)
  trans := by
    intro S H Δ j hΔ h
    apply h.bind
    rintro q ⟨φ, hφ, rfl⟩
    rcases hφ with hφ | hφ
    · exact .hyp ⟨φ, hφ, rfl⟩
    · exact hΔ φ hφ
  map_derives := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ σ H j h
    rw [Subsingleton.elim σ (𝟙 _), CategoryTheory.Functor.map_id]
    simpa using h

/-- Adding universes preserves bounded derivability as well as satisfaction. -/
def inclusionLogical {n m : ℕ} (h : n ≤ m) :
    LogicalSystem.CoHom (logic.{u} n) (logic.{u} m) where
  Φ := 𝟭 _
  ρ := (inclusion h).ρ
  map_derives := by
    intro S H j d
    change Set (Sentence n) at H
    change Sentence n at j
    change Ctx.JEqB n (Subtype.val '' H) j.val.Γ j.val.A j.val.a j.val.b at d
    change Ctx.JEqB m (Subtype.val '' (includeSentence h '' H)) _ _ _ _
    have hi : Subtype.val '' (includeSentence h '' H) = Subtype.val '' H := by
      rw [← Set.image_comp]
      rfl
    rw [hi]
    exact d.include h

/-- The logical-system inclusion that adds one available universe. -/
def successorLogical (n : ℕ) : LogicalSystem.CoHom (logic.{u} n) (logic.{u} (n + 1)) :=
  inclusionLogical (Nat.le_succ n)

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite
