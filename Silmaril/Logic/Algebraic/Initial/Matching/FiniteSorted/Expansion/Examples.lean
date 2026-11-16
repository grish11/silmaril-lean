module

public import Silmaril.Logic.Algebraic.Initial.Matching.FiniteSorted.Expansion.Thms
public import Silmaril.Logic.Algebraic.Initial.Matching.FiniteSorted.Examples
import Lean

/-! Concrete global expansion controls. The positive model is the actual free
ground-term algebra for a seeded finite two-sort profile. The negative model
collapses both source sorts and unary symbols in the numeric ambient algebra.
All existing general results retain arbitrary contexts and ambient maps.
These authored controls make no assertion that a build has been executed. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.Examples
open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Institution.Structured
open Silmaril.Logic.Matching
open Initial.Presented Initial.Presented.Characterization

open Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Examples

/-- Original S/T constructors, no equations, and the identity ambient context. -/
def freeSentence : Sentence seeded.signature :=
  ⟨seeded, ∅, 𝟙 seeded.signature⟩

abbrev freeAmbient : EQ.Algebra seeded.signature :=
  Initial.closedAlgebra seeded.signature

/-- This concrete positive model has ground constructors in both original sorts. -/
theorem free_carriers_inhabited :
    Nonempty (freeAmbient.carrier (0 : Fin 2)) ∧
      Nonempty (freeAmbient.carrier (1 : Fin 2)) :=
  ⟨⟨zeroGround⟩, ⟨oneGround⟩⟩

/-- Actual initiality among all public algebras of this original signature. -/
def free_isInitial : IsInitial freeAmbient :=
  Initial.closed_isInitial seeded.signature

theorem free_source_satisfaction : freeSentence.Satisfies freeAmbient := by
  change Constraints.Sat Initial.equational freeAmbient
    (Constraints.translate Initial.equational (𝟙 seeded.signature)
      (Initial.initialConstraint (theory seeded ∅)))
  erw [Constraints.translate_id]
  exact Initial.closedModel_satisfies seeded.signature

def freeNative : SignedSpectrum.NativeModel seeded.signature :=
  expandModel freeAmbient

/-- Positive global-interface control for the COMPLETE compiled clause set. -/
theorem free_compiled_satisfaction :
    (theoryRoom seeded.signature).Sat freeNative freeSentence.compile :=
  (expandModel_satisfaction freeAmbient freeSentence).mpr free_source_satisfaction

/-- Independently expose the global compiler satisfaction interface at its
actual decoded object, rather than identifying that active subtype with syntax. -/
theorem free_decoded_satisfaction :
    freeSentence.Satisfies (SignedSpectrum.decode freeNative) :=
  (Sentence.compile_satisfaction freeNative freeSentence).mp free_compiled_satisfaction

/-- Both directions are actual algebra arrows from the global natural iso. -/
def freeDecodeForward : SignedSpectrum.decode freeNative ⟶ freeAmbient :=
  (expansionDecodeIso seeded.signature).hom.app freeAmbient

def freeDecodeBackward : freeAmbient ⟶ SignedSpectrum.decode freeNative :=
  (expansionDecodeIso seeded.signature).inv.app freeAmbient

theorem freeDecode_forward_backward :
    freeDecodeForward ≫ freeDecodeBackward = 𝟙 (SignedSpectrum.decode freeNative) :=
  (decodeExpandIso freeAmbient).hom_inv_id

theorem freeDecode_backward_forward :
    freeDecodeBackward ≫ freeDecodeForward = 𝟙 freeAmbient :=
  (decodeExpandIso freeAmbient).inv_hom_id

/-- Evaluate the actual free algebra in the collapsed numeric source reduct. -/
def freeFold : freeAmbient ⟶ numericSource :=
  Initial.foldHom numericSource (fun i => i.elim0)

theorem freeFold_zero : freeFold.map (0 : Fin 2) zeroGround = (0 : Nat) := rfl
theorem freeFold_two : freeFold.map (0 : Fin 2) twoGround = (2 : Nat) := rfl

def expandedFold : freeNative ⟶ expandModel numericSource :=
  (expandModels seeded.signature).map freeFold

/-- The concrete nonidentity evaluation arrow satisfies the FULL global
natural-isomorphism square, including its carrier and operation laws. -/
theorem expandedFold_naturality :
    (decodeModels seeded.signature).map expandedFold ≫
        (expansionDecodeIso seeded.signature).hom.app numericSource =
      freeDecodeForward ≫ freeFold :=
  (expansionDecodeIso seeded.signature).hom.naturality freeFold

/-- Same original finite presentation, now in a context identifying both sorts
and both unary symbols. The whole ambient Nat carrier remains the source model. -/
def collapsedSentence : Sentence collapsedSignature :=
  ⟨seeded, ∅, collapse⟩

theorem collapsed_expansion_is_existing_control :
    expandModel numericAmbient = numericNative := rfl

/-- Original S is not generated: 1 is active but every original S ground term
has even numeric value. This refutes the entire compiled global theory. -/
theorem collapsed_compiled_false :
    ¬ (theoryRoom collapsedSignature).Sat numericNative collapsedSentence.compile := by
  intro h
  have hc : Satisfies numericNative (compiled (∅ : Set (Equations seeded)) collapse) := h
  have generatedAll := ((compiled_satisfaction (∅ : Set (Equations seeded))
    collapse numericNative).mp hc).1
  let activeOne : (reduct collapse numericNative).carrier (0 : Fin 2) :=
    ⟨some (1 : Nat), ⟨(1 : Nat), rfl⟩⟩
  obtain ⟨t, ht⟩ := generatedAll (0 : Fin 2) activeOne
  apply one_not_in_coordinate_zero
  apply Eq.mp (congrArg (fun X => (some 1 : Option Nat) ∈ X)
    (generated_denote collapse numericNative (0 : Fin 2))).symm
  exact ⟨t, congrArg Subtype.val ht⟩

/-- The actual source global sentence is false in numericAmbient itself. -/
theorem collapsed_source_false :
    ¬ collapsedSentence.Satisfies numericAmbient := by
  intro h
  exact collapsed_compiled_false
    ((expandModel_satisfaction numericAmbient collapsedSentence).mpr h)

/-- The actual decoded model also fails, by Sentence.compile_satisfaction. -/
theorem collapsed_decoded_false :
    ¬ collapsedSentence.Satisfies (SignedSpectrum.decode numericNative) := by
  intro h
  exact collapsed_compiled_false
    ((Sentence.compile_satisfaction numericNative collapsedSentence).mpr h)

def numericDecodeForward : SignedSpectrum.decode numericNative ⟶ numericAmbient :=
  (expansionDecodeIso collapsedSignature).hom.app numericAmbient

def numericDecodeBackward : numericAmbient ⟶ SignedSpectrum.decode numericNative :=
  (expansionDecodeIso collapsedSignature).inv.app numericAmbient

theorem numericDecode_forward_backward :
    numericDecodeForward ≫ numericDecodeBackward = 𝟙 (SignedSpectrum.decode numericNative) :=
  (decodeExpandIso numericAmbient).hom_inv_id

theorem numericDecode_backward_forward :
    numericDecodeBackward ≫ numericDecodeForward = 𝟙 numericAmbient :=
  (decodeExpandIso numericAmbient).inv_hom_id

#print axioms free_source_satisfaction
#print axioms free_compiled_satisfaction
#print axioms free_decoded_satisfaction
#print axioms freeDecode_forward_backward
#print axioms freeDecode_backward_forward
#print axioms expandedFold_naturality
#print axioms collapsed_compiled_false
#print axioms collapsed_source_false
#print axioms collapsed_decoded_false
#print axioms numericDecode_forward_backward
#print axioms numericDecode_backward_forward

/- Exact dependency sets observed for all eleven declarations in normal CI
run 43251991871. -/
run_elab do
  let selected : Array Lean.Name := #[
    ``free_source_satisfaction,
    ``free_compiled_satisfaction,
    ``free_decoded_satisfaction,
    ``freeDecode_forward_backward,
    ``freeDecode_backward_forward,
    ``expandedFold_naturality,
    ``collapsed_compiled_false,
    ``collapsed_source_false,
    ``collapsed_decoded_false,
    ``numericDecode_forward_backward,
    ``numericDecode_backward_forward]
  let expected : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in selected do
    let actual ← Lean.collectAxioms declaration
    unless actual.size == expected.size && actual.all (fun ax => expected.contains ax) do
      throwError "Axiom set changed for {declaration}: {actual}; expected {expected}"

end Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.Examples
