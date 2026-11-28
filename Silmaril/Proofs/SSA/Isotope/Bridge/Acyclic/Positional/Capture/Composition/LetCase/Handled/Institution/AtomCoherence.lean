module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory Silmaril.Elgot
open LambdaSSA.Semantics.Categorical (ofMonadicTypeModel ofMonadicInstructionModel RegionTypingCoherent)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues typeModel)
open Isotope.Semantics (encodeValue encodeValue_injective InstructionModel)
open LetIter.Semantics.Categorical (ofTypeModel ofInstructionModel)
open LetSeq.StraightLine.Structural (Trace model)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)
open Silmaril.Semantics.NondeterministicTrace (Finite)
open scoped LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Carriers

attribute [local instance] typeModel

variable {κ : Type} [AtomValues κ]

local notation "W" => AtomValues.carrier (κ := κ)

private theorem typeModel_eq : ofMonadicTypeModel (τ := Ty κ) = ofTypeModel (Ty.denote W) := by
  unfold ofMonadicTypeModel LambdaSSA.Subtyping.Semantics.Categorical.exactTypeModel
    LetIter.ProofRelevant.Semantics.Categorical.ofTypeModel
    LetIter.Semantics.Categorical.ofTypeModel
  congr 1
  exact Subsingleton.elim _ _

variable {m : Type → Type} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  {Φ : Type} [HasTy Φ (Ty κ)] [HasEff Φ Bool]

/-- The free-type interpretation over any atom carriers has unique native
region arrows. This is the existing argument for the atom-free types, with
the erasure taken at the given carriers. -/
private theorem regionCoherent (M : InstructionModel (Ty.denote W) Φ m)
    (pureM : InstructionModel.RespectsPure (ε := Bool) M) (bad : {X : Type} → m X) :
    letI := ofInstructionModel (Ty.denote W) M
    RegionTypingCoherent (Φ := Φ) (Kleisli.Adjunction.toKleisli (ofTypeMonad m)) (ofTypeModel (Ty.denote W)) := by
  classical
  let _ : LetIter.ProofRelevant.Semantics.InstructionModel Φ (Ty κ) Bool m :=
    ⟨M.eval, (fun f h => (pureM f h).choose), (fun f h x => (pureM f h).choose_spec x)⟩
  let raw (f : Φ) (x : Value (Sigma W)) : m (Value (Sigma W)) :=
    if h : ∃ a, encodeValue W (instrSrc f) a = x then
      M.eval f h.choose >>= fun y => pure (encodeValue W (instrTrg f) y)
    else bad
  have compatible (f : Φ) (x : Ty.denote W (instrSrc f)) :
      raw f (encodeValue W (instrSrc f) x) =
        (M.eval f x >>= fun y => pure (encodeValue W (instrTrg f) y)) := by
    let h : ∃ a, encodeValue W (instrSrc f) a = encodeValue W (instrSrc f) x := ⟨x, rfl⟩
    unfold raw
    rw [dite_eq_left h, encodeValue_injective W _ h.choose_spec]
  have coherent := LambdaSSA.Semantics.Erasure.regionTypingCoherent
    (κ := κ) (m := m) raw bad bad compatible
  let Types := LetIter.Semantics.Categorical.TypeModel (Ty κ) Type
  let J := Kleisli.Adjunction.toKleisli (ofTypeMonad m)
  let Instr (T : Types) := LetIter.Semantics.Categorical.InstructionModel J T Φ
  let arrow {T : Types} (I : Instr T) (f : Φ) :=
    LetIter.Semantics.Categorical.InstructionModel.denote (self := I) f
  let coherentModel (T : Types) (I : Instr T) :=
    letI _ : LetIter.Semantics.Categorical.InstructionModel J T Φ := I
    RegionTypingCoherent (Φ := Φ) J T
  have transport {T U : Types} (e : T = U) (I : Instr T) (K : Instr U)
      (same : ∀ f, HEq (arrow I f) (arrow K f))
      (h : coherentModel T I) : coherentModel U K := by
    cases e
    have eq : I = K := by
      cases I
      cases K
      congr 1
      funext f
      exact eq_of_heq (same f)
    cases eq
    exact h
  exact transport typeModel_eq (ofMonadicInstructionModel (τ := Ty κ) (ε := Bool) (m := m))
    (ofInstructionModel (Ty.denote W) M) (fun _ => HEq.rfl) coherent

end Carriers

/-- The ordered trace interpretation whose atoms are natural numbers has
coherent native region witnesses. -/
theorem atomTrace_region_coherent_proof {α Φ : Type} [HasTy Φ (Ty α)] :
    letI := traceInstructions (α := α) (Φ := Φ)
    RegionTypingCoherent (Φ := Φ) (traceJ (α := α) (Φ := Φ)) (traceTypes α) := by
  let _ : AtomValues α := ⟨fun _ => Nat⟩
  exact regionCoherent (κ := α) (m := Trace α Φ) model (fun f h => by cases h)
    (fun {_} => Finite.ofOutcomes ∅)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
