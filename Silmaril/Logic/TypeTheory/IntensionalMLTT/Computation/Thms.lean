module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Regularity
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Computation

public section

/-!
# Typed computation for the intensional beta rules

All six primitive computation schemes have correctly typed contracta from
their ordinary formation premises. The dependent second projection uses
conversion congruence under instantiation; the Nat successor case checks the
predecessor and recursive-result substitutions of its step type. These are
root computation theorems. General subject reduction for arbitrary derivation
trees still requires generation and raw-conversion injectivity/confluence.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Pointwise convertible assignments give convertible substituted terms. -/
noncomputable def Term.subst_conversion {n m : ℕ} (t : Term n) {σ τ : Fin n → Term m}
    (h : ∀ i, Conversion (σ i) (τ i)) : Conversion (t.subst σ) (t.subst τ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Computation.conversion_subst_congr t h

/-- A dependent motive respects conversion of its instantiated argument. -/
noncomputable def Term.instantiate_conversion {n : ℕ} (t : Term (n + 1)) {a b : Term n}
    (h : Conversion a b) : Conversion (t.instantiate a) (t.instantiate b) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Computation.conversion_instantiate t h

/-- First projection computation preserves the declared domain type. -/
theorem TypedEq.fst_pair {n i j : ℕ} {Γ : Context n} {A a b : Term n} {B : Term (n + 1)}
    (hA : Derivation Γ A (.univ i)) (hB : Derivation (Γ.snoc A) B (.univ j))
    (ha : Derivation Γ a A) (hb : Derivation Γ b (B.instantiate a)) :
    TypedEq Γ (.fst (.pair a b)) a A :=
  ⟨⟨.fst (.pair hA hB ha hb)⟩, ⟨ha⟩, ⟨.fst_pair a b⟩⟩

/-- Second projection computation preserves the dependent source type. -/
theorem TypedEq.snd_pair {n i j : ℕ} {Γ : Context n} {A a b : Term n} {B : Term (n + 1)}
    (hA : Derivation Γ A (.univ i)) (hB : Derivation (Γ.snoc A) B (.univ j))
    (ha : Derivation Γ a A) (hb : Derivation Γ b (B.instantiate a)) :
    TypedEq Γ (.snd (.pair a b)) b (B.instantiate (.fst (.pair a b))) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Computation.snd_pair_typed hA hB ha hb

/-- Natural recursion at zero has the type of its base case. -/
theorem TypedEq.nat_zero {n i : ℕ} {Γ : Context n} {C : Term (n + 1)} {z s : Term n}
    (hC : Derivation (Γ.snoc .nat) C (.univ i))
    (hz : Derivation Γ z (C.instantiate .zero)) (hs : Derivation Γ s C.natStepType) :
    TypedEq Γ (.natrec C z s .zero) z (C.instantiate .zero) :=
  ⟨⟨.natrec hC hz hs (.zero hz.context)⟩, ⟨hz⟩, ⟨.nat_zero C z s⟩⟩

/-- Natural recursion at successor types the predecessor and recursive result. -/
theorem TypedEq.nat_succ {n i : ℕ} {Γ : Context n} {C : Term (n + 1)} {z s t : Term n}
    (hC : Derivation (Γ.snoc .nat) C (.univ i))
    (hz : Derivation Γ z (C.instantiate .zero)) (hs : Derivation Γ s C.natStepType)
    (ht : Derivation Γ t .nat) :
    TypedEq Γ (.natrec C z s (.succ t)) (.app (.app s t) (.natrec C z s t))
      (C.instantiate (.succ t)) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Computation.nat_succ_typed hC hz hs ht

/-- Based J at reflexivity has the type of its given base case. -/
theorem TypedEq.j_refl {n i j : ℕ} {Γ : Context n} {A a d : Term n} {C : Term (n + 2)}
    (hA : Derivation Γ A (.univ i)) (ha : Derivation Γ a A)
    (hC : Derivation (motiveContext Γ A a) C (.univ j))
    (hd : Derivation Γ d (C.instantiate₂ a (.refl a))) :
    TypedEq Γ (.j A a C d a (.refl a)) d (C.instantiate₂ a (.refl a)) :=
  ⟨⟨.j hA ha hC hd ha (.refl hA ha)⟩, ⟨hd⟩, ⟨.j_refl A a C d⟩⟩

end Silmaril.Logic.TypeTheory.IntensionalMLTT
