module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.FiniteSoundness.Defs
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityFiniteSoundness

public section

/-!
# Actual finite-code soundness for the original cumulative calculus

A proof whose complete original proof tree fits cap is interpreted with actual
Code cap carriers and context declarations. The source rules and arbitrary raw
conversion are unchanged. No eventual code stage is substituted for that cap.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Every original hypothetical rule is valid in the specified concrete finite code stage. -/
theorem DerivationH.realizesAt {cap : ℕ} {H : Set ScopedTyping} {n : ℕ}
    {Γ : Context n} {t A : Term n} (d : DerivationH H Γ t A)
    (hBudget : d.universeBudget ≤ cap)
    (hH : ∀ q ∈ H, RawRealizability.ValidAt cap q.Γ q.term q.carrier) :
    RawRealizability.ValidAt cap Γ t A :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityFiniteSoundness.realizes
    d cap hBudget hH

/-- A bounded original hypothetical proof is sound in every actual larger finite code cap. -/
theorem BoundedDerivationH.realizesAt {levels cap : ℕ} {H : Set ScopedTyping} {n : ℕ}
    {Γ : Context n} {t A : Term n} (d : BoundedDerivationH levels H Γ t A)
    (h : levels ≤ cap) (hH : ∀ q ∈ H, RawRealizability.ValidAt cap q.Γ q.term q.carrier) :
    RawRealizability.ValidAt cap Γ t A := d.val.realizesAt (d.property.trans h) hH

/-- Actual finite-code soundness for a bounded unchanged original derivation. -/
theorem BoundedDerivation.realizesAt {levels cap n : ℕ} {Γ : Context n} {t A : Term n}
    (d : BoundedDerivation levels Γ t A) (h : levels ≤ cap) :
    RawRealizability.ValidAt cap Γ t A :=
  (show BoundedDerivationH levels ∅ Γ t A from .ofOriginal d).realizesAt h
    (fun _ hq => False.elim hq)

namespace RawRealizability

/-- At a concrete finite cap, universe membership has the exact strict source index. -/
theorem RealizesAt.univ_iff {cap n i : ℕ} {A : Term n} {ρ : Environment n 0} :
    RealizesAt cap A (.univ i) ρ ↔ i < cap ∧ ∃ X, Code i (eval A ρ) X :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityFiniteSoundness.univ_iff

/-- A finite-stage assignment is also an actual assignment in the full code hierarchy. -/
theorem RealizesContextAt.forget {cap n : ℕ} {Γ : Context n} {ρ : Environment n 0}
    (h : RealizesContextAt cap Γ ρ) : RealizesContext Γ ρ := by
  induction Γ with
  | nil => trivial
  | snoc Γ A ih =>
    rcases h with ⟨hΓ, X, hX, hx⟩
    exact ⟨ih hΓ, cap, X, hX, hx⟩

/-- Finite-stage membership remains actual membership in the full hierarchy. -/
theorem RealizesAt.forget {cap n : ℕ} {t A : Term n} {ρ : Environment n 0}
    (h : RealizesAt cap t A ρ) : Realizes t A ρ := by
  rcases h with ⟨X, hX, ht⟩
  exact ⟨cap, X, hX, ht⟩

/-- No concrete finite code stage has an Empty realizer. -/
theorem no_empty_at {cap n : ℕ} (t : Term n) (ρ : Environment n 0) :
    ¬ RealizesAt cap t .empty ρ := by
  rintro ⟨X, hX, ht⟩
  exact hX.no_empty_realizer _ ht

end RawRealizability
end Silmaril.Logic.TypeTheory.IntensionalMLTT
