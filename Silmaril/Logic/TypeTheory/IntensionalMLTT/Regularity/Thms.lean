module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Substitution
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Regularity

public section

/-!
# Context and type regularity for the intensional core

Every typing derivation has a well-formed context, and its type itself has a
universe typing. The proofs use admissible substitution for applications,
dependent projections, Nat recursion and the two-binder J motive. Formation
inversion here concerns a syntactic Π or Σ term, including derivations ending
in conversion or cumulativity. It does not assume injectivity of Π/Σ under raw
conversion, or establish general subject reduction.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- The telescope of an actual typing tree has a well-formedness derivation. -/
noncomputable def Derivation.context {n : ℕ} {Γ : Context n} {t A : Term n}
    (h : Derivation Γ t A) : ContextDerivation Γ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Regularity.derivation_context h

/-- The endpoint and path of an identity proof give the actual J substitution. -/
noncomputable def Substitution.motive {n : ℕ} {Γ : Context n} {A a b p : Term n}
    (hb : Derivation Γ b A) (hp : Derivation Γ p (.id A a b)) :
    Substitution (motiveContext Γ A a) Γ (Fin.cons p (Fin.cons b Term.var)) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Regularity.motive_substitution hb.context hb hp

/-- A typed J motive instance retains its exact substituted carrier. -/
noncomputable def Derivation.instantiate₂ {n : ℕ} {Γ : Context n}
    {A a b p : Term n} {t T : Term (n + 2)}
    (h : Derivation (motiveContext Γ A a) t T)
    (hb : Derivation Γ b A) (hp : Derivation Γ p (.id A a b)) :
    Derivation Γ (t.instantiate₂ b p) (T.instantiate₂ b p) :=
  h.subst hb.context _ (Substitution.motive hb hp)

/-- Every declaration retrieved from a well-formed telescope has a universe type. -/
theorem Lookup.formation {n : ℕ} {Γ : Context n} {i : Fin n} {A : Term n}
    (hi : Lookup Γ i A) (hΓ : ContextDerivation Γ) : ∃ level, Typing Γ A (.univ level) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Regularity.lookup_formation hi hΓ

/-- A syntactic Π type has domain and codomain formation derivations. -/
theorem Derivation.pi_formation {n : ℕ} {Γ : Context n} {A T : Term n} {B : Term (n + 1)}
    (h : Derivation Γ (.pi A B) T) :
    ∃ i j, Typing Γ A (.univ i) ∧ Typing (Γ.snoc A) B (.univ j) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Regularity.pi_formation h rfl

/-- A syntactic Σ type has domain and codomain formation derivations. -/
theorem Derivation.sigma_formation {n : ℕ} {Γ : Context n} {A T : Term n} {B : Term (n + 1)}
    (h : Derivation Γ (.sigma A B) T) :
    ∃ i j, Typing Γ A (.univ i) ∧ Typing (Γ.snoc A) B (.univ j) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Regularity.sigma_formation h rfl

/-- A syntactic identity type has actual carrier formation and both endpoint typings. -/
theorem Derivation.id_formation {n : ℕ} {Γ : Context n} {A a b T : Term n}
    (h : Derivation Γ (.id A a b) T) :
    ∃ i, Typing Γ A (.univ i) ∧ Typing Γ a A ∧ Typing Γ b A :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Regularity.id_formation h rfl

/-- Every derived type is itself derivably an element of some universe. -/
theorem Derivation.type_formation {n : ℕ} {Γ : Context n} {t A : Term n}
    (h : Derivation Γ t A) : ∃ level, Typing Γ A (.univ level) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Regularity.type_formation h

/-- Typability entails well-formedness of the telescope. -/
theorem Typing.wellFormed {n : ℕ} {Γ : Context n} {t A : Term n}
    (h : Typing Γ t A) : WellFormed Γ := by
  obtain ⟨ht⟩ := h
  exact ⟨ht.context⟩

/-- Proposition-level form of universe regularity. -/
theorem Typing.type_formation {n : ℕ} {Γ : Context n} {t A : Term n}
    (h : Typing Γ t A) : ∃ level, Typing Γ A (.univ level) := by
  obtain ⟨ht⟩ := h
  exact ht.type_formation

/-- The common type in typed beta equality has an actual universe derivation. -/
theorem TypedEq.type_formation {n : ℕ} {Γ : Context n} {t u A : Term n}
    (h : TypedEq Γ t u A) : ∃ level, Typing Γ A (.univ level) :=
  h.1.type_formation

end Silmaril.Logic.TypeTheory.IntensionalMLTT
