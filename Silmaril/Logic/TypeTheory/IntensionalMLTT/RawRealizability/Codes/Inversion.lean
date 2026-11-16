module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Codes.Thms
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodeInversion

public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

/-- A universe code has its exact strict index and actual lower-stage code set. -/
theorem Code.univ_inv {i j : ℕ} {X : Set (Value 0)} (h : Code i (RawRealizability.univ j) X) :
    j < i ∧ X = {q | ∃ Y, Code j q Y} :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodeInversion.univ_inv h

/-- Product-code inversion recovers the actual domain and every inhabited codomain fibre. -/
theorem Code.pi_inv {i : ℕ} {A : Value 0} {B : Value 1} {T : Set (Value 0)}
    (h : Code i (RawRealizability.pi A B) T) :
    ∃ X Y, Code i A X ∧ (∀ a ∈ X, Code i (instantiate B a) (Y a)) ∧ T = FunctionSpace X Y :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodeInversion.pi_inv h

/-- Sum-code inversion recovers actual domain and fibre interpretation. -/
theorem Code.sigma_inv {i : ℕ} {A : Value 0} {B : Value 1} {T : Set (Value 0)}
    (h : Code i (RawRealizability.sigma A B) T) :
    ∃ X Y, Code i A X ∧ (∀ a ∈ X, Code i (instantiate B a) (Y a)) ∧ T = PairSpace X Y :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodeInversion.sigma_inv h

/-- Identity-code inversion retains both actual endpoint memberships. -/
theorem Code.id_inv {i : ℕ} {A a b : Value 0} {T : Set (Value 0)}
    (h : Code i (RawRealizability.id A a b) T) :
    ∃ X, Code i A X ∧ a ∈ X ∧ b ∈ X ∧ T = IdentitySpace a b :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodeInversion.id_inv h

end Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability
