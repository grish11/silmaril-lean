module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Codes.Defs
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Algebra.Thms
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes

public section

/-!
# Functional cumulative codes and original raw-conversion invariance

These are actual recursively constructed realizer sets in the concrete target
quotient, not fields postulating soundness. Cross-level functionality and
cumulative lifting are proved. Original raw conversion preserves a code by its
one-way embedding into that quotient. The original-rule fundamental theorem,
raw Empty consistency and checked reification are not asserted in this slice.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

/-- Unfold only the current stage; its universe dependencies remain strictly lower stages. -/
theorem Code.iff_layer {i : ℕ} {q : Value 0} {X : Set (Value 0)} :
    Code i q X ↔ CodeLayer i (fun k _ => Code k) q X :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes.code_iff_layer

/-- A concrete quotient type has exactly one realizer set, independently of code level. -/
theorem Code.functional {i j : ℕ} {q : Value 0} {X Y : Set (Value 0)}
    (hX : Code i q X) (hY : Code j q Y) : X = Y :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes.code_functional hX hY

theorem Code.nat (i : ℕ) : Code i nat Naturals :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes.code_nat i

theorem Code.empty (i : ℕ) : Code i empty ∅ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes.code_empty i

theorem Code.unit (i : ℕ) : Code i unit Units :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes.code_unit i

theorem Code.univ {i j : ℕ} (h : j < i) :
    Code i (univ j) {q | ∃ X, Code j q X} :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes.code_univ h

theorem Code.pi {i : ℕ} {A : Value 0} {B : Value 1} {X : Set (Value 0)}
    {Y : Value 0 → Set (Value 0)} (hA : Code i A X)
    (hB : ∀ a ∈ X, Code i (instantiate B a) (Y a)) :
    Code i (pi A B) (FunctionSpace X Y) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes.code_pi hA hB

theorem Code.sigma {i : ℕ} {A : Value 0} {B : Value 1} {X : Set (Value 0)}
    {Y : Value 0 → Set (Value 0)} (hA : Code i A X)
    (hB : ∀ a ∈ X, Code i (instantiate B a) (Y a)) :
    Code i (sigma A B) (PairSpace X Y) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes.code_sigma hA hB

theorem Code.id {i : ℕ} {A a b : Value 0} {X : Set (Value 0)}
    (hA : Code i A X) (ha : a ∈ X) (hb : b ∈ X) : Code i (id A a b) (IdentitySpace a b) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes.code_id hA ha hb

/-- Code cumulativity preserves the actual interpreted set. -/
theorem Code.lift {i j : ℕ} {q : Value 0} {X : Set (Value 0)} (h : Code i q X) (hij : i ≤ j) :
    Code j q X :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes.code_lift h hij

/-- Every existing original raw conversion preserves actual target code interpretation. -/
theorem Code.of_raw_conversion {i : ℕ} {A B : Term 0} {X : Set (Value 0)}
    (h : Convertible A B) (hA : Code i (ofTerm A) X) : Code i (ofTerm B) X :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes.raw_conversion_invariant h hA

/-- Every code for the original Empty constructor denotes the actual empty set. -/
theorem Code.empty_meaning {i : ℕ} {X : Set (Value 0)} (h : Code i RawRealizability.empty X) : X = ∅ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes.empty_meaning h

/-- The actual Empty code admits no quotient-term realizer. -/
theorem Code.no_empty_realizer {i : ℕ} {X : Set (Value 0)} (h : Code i RawRealizability.empty X) (q : Value 0) : q ∉ X :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityCodes.no_empty_realizer h q

end Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability
