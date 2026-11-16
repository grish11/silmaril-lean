module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Soundness.Defs
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness

public section

/-!
# Realizability of every original cumulative intensional typing rule

The unchanged original derivations, including arbitrary raw conversion, cumulative
universes and exact based J, inhabit the actual quotient realizer sets. In
particular the original empty context cannot derive an Empty inhabitant. This
model theorem does not assert original confluence, normalization, conversion
conservativity, or a checked reification/completeness theorem.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- The full original typing derivation is valid in the concrete realizability model. -/
theorem Derivation.realizes {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : Derivation Γ t A) : RawRealizability.Valid Γ t A :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.realizes d

/-- The proof-forgetting original typing proposition also has actual realizability soundness. -/
theorem Typing.realizes {n : ℕ} {Γ : Context n} {t A : Term n}
    (h : Typing Γ t A) : RawRealizability.Valid Γ t A := by
  rcases h with ⟨d⟩
  exact d.realizes

namespace RawRealizability

/-- A closed original derivation supplies an actual code and quotient realizer. -/
theorem closed_realizes {t A : Term 0} (d : Derivation .nil t A) :
    ∃ i X, Code i (ofTerm A) X ∧ ofTerm t ∈ X := by
  have h := d.realizes (variableEnv 0) trivial
  simpa only [Realizes, eval_identity] using h

/-- No original closed term inhabits Empty, without restricting conversion nodes. -/
theorem no_closed_empty (t : Term 0) : ¬ Typing .nil t .empty :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.no_closed_empty t

/-- Closed consistency of the unchanged original cumulative intensional core. -/
theorem empty_consistency : ¬ ∃ t : Term 0, Typing .nil t .empty := by
  rintro ⟨t, ht⟩
  exact no_closed_empty t ht

end RawRealizability
end Silmaril.Logic.TypeTheory.IntensionalMLTT
