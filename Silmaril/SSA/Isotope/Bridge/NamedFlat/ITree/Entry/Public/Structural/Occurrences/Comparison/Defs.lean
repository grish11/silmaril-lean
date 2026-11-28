module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Refinement.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Witness.Thms

/-! # Checked structural RTL comparison at generated occurrence entries -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.Logic.ITree
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

/-- Exact admissions of both generated endpoints of a structural comparison. -/
structure OccurrenceComparison where
  leftAdmission : OccurrenceAdmission left
  rightAdmission : OccurrenceAdmission right

/-- Test both dispatcher packet types and derive the occurrence admissions.
A missing result reports an unsupported packet type before considering any store. -/
def StructuralEntry.checkOccurrenceComparison? : Option (OccurrenceComparison left right) :=
  if l : left.entry.context.get left.provenance.slot = inputType then
    if r : right.entry.context.get right.provenance.slot = rightType then
      some ⟨left.admittedOccurrences l, right.admittedOccurrences r⟩
    else none
  else none

variable {left right}

namespace OccurrenceComparison

/-- The existing handled-trace sentence at the independently decoded packets. -/
noncomputable def sentence (checked : OccurrenceComparison left right)
    (a : Denote inputType) (b : Denote rightType) :
    TraceInstitution.Sentence.{0, 1} signature.traceSignature :=
  checked.leftAdmission.refinementSentence checked.rightAdmission a b

/-- At a checked pair of endpoints, a missing pointwise verdict means that
at least one seed failed to decode. A false verdict is semantic rejection. -/
def fromStore? [DecidableEq F] (_checked : OccurrenceComparison left right)
    (initial : V → Value Atom) : Option Bool :=
  left.refinementFromStore? right initial

/-- Compare all jointly decodable stores, retaining the separate empty-domain flag. -/
def overCaptures [DecidableEq F] (_checked : OccurrenceComparison left right) : CaptureRefinement :=
  left.refinementOverCaptures right

/-- Retrieve the original named representative and directed trace, with its
refutation of the RTL runners. The same witness refutes the occurrence sentence. -/
def counterexample? [DecidableEq F] (_checked : OccurrenceComparison left right) :
    Option {witness : CaptureTraceWitness V signature // witness.Refutes left right} :=
  left.refinementCounterexample? right

end OccurrenceComparison
end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
