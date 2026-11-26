module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Semantics.Categorical (ofMonadicTypeModel ofMonadicInstructionModel RegionTypingCoherent)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues typeModel)
open Isotope.Semantics (encodeValue)
open LetIter.ProofRelevant.Semantics (InstructionModel)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : AtomValues Empty := ⟨Empty.elim⟩
attribute [local instance] typeModel

private instance instructions : InstructionModel signature.Instr Sorts Bool Trace where
  denote := model.eval
  denotePure f h := by cases f <;> cases h
  denote_pure f h := by cases f <;> cases h

/-- Both interpretations choose the same structural coordinates on free
types. Initiality provides the last equality of the chosen structure. -/
private theorem typeModel_eq : ofMonadicTypeModel (τ := Sorts) = traceTypes := by
  unfold ofMonadicTypeModel LambdaSSA.Subtyping.Semantics.Categorical.exactTypeModel
    LetIter.ProofRelevant.Semantics.Categorical.ofTypeModel traceTypes
    LetIter.Semantics.Categorical.ofTypeModel
  congr 1
  exact Subsingleton.elim _ _

private def raw (f : signature.Instr) (_ : Value (Sigma (AtomValues.carrier (κ := Empty)))) :
    Trace (Value (Sigma (AtomValues.carrier (κ := Empty)))) :=
  model.eval f PUnit.unit >>= fun x => pure (encodeValue (Empty.elim : Empty → Type) _ x)

private def noResult {A : Type} : Trace A :=
  ExceptT.mk (WriterT.mk Part.none)

theorem traceRegionCoherent_proof :
    letI := traceInstructions
    RegionTypingCoherent (Φ := signature.Instr) traceJ traceTypes := by
  have compatible (f : signature.Instr) (x : value (instrSrc f)) :
      raw f (encodeValue (Empty.elim : Empty → Type) _ x) =
        (model.eval f x >>= fun y => pure (encodeValue (Empty.elim : Empty → Type) _ y)) := by
    cases f <;> cases x <;> rfl
  have coherent := LambdaSSA.Semantics.Erasure.regionTypingCoherent
    (κ := Empty) (m := Trace) raw noResult noResult compatible
  let Types := LetIter.Semantics.Categorical.TypeModel Sorts Type
  let Instr (M : Types) := LetIter.Semantics.Categorical.InstructionModel traceJ M signature.Instr
  let arrow {M : Types} (I : Instr M) (f : signature.Instr) :=
    LetIter.Semantics.Categorical.InstructionModel.denote (self := I) f
  let coherentModel (M : Types) (I : Instr M) :=
    letI _ : LetIter.Semantics.Categorical.InstructionModel traceJ M signature.Instr := I
    RegionTypingCoherent (Φ := signature.Instr) traceJ M
  have transport {M N : Types} (e : M = N) (I : Instr M) (K : Instr N)
      (same : ∀ f, HEq (arrow I f) (arrow K f))
      (h : coherentModel M I) : coherentModel N K := by
    cases e
    have eq : I = K := by
      cases I
      cases K
      congr 1
      funext f
      exact eq_of_heq (same f)
    cases eq
    exact h
  exact transport typeModel_eq (ofMonadicInstructionModel (τ := Sorts) (ε := Bool) (m := Trace))
    traceInstructions (fun _ => HEq.rfl) coherent

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence
