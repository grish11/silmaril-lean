module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Refinement.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Refinement

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.Elgot.ITree (HandledTrace)
open Silmaril.Logic.ITree
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  {left : StructuralEntry signature source exits fields inputType outputs}
  {right : StructuralEntry signature target exits fields rightType outputs}
  (leftAdmission : OccurrenceAdmission left) (rightAdmission : OccurrenceAdmission right)

/-- At the two checked decodings of one store, the occurrence-entry
sentence is the existing versioned-SSA sentence. -/
theorem OccurrenceAdmission.refinementSentence_eq_versioned
    (initial : V → Value Atom) (a : Denote inputType) (b : Denote rightType)
    (ha : left.seed? initial = some a) (hb : right.seed? initial = some b) :
    leftAdmission.refinementSentence rightAdmission a b = left.versionedRefinementSentence right initial :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Refinement.sentence_eq leftAdmission rightAdmission initial a b ha hb

/-- A Boolean verdict at one store requires both decodings. With those
packets, a true verdict is exactly validity across shared reply policies. -/
theorem OccurrenceAdmission.refinementFromStore?_eq_some_iff [DecidableEq F]
    (initial : V → Value Atom) (verdict : Bool) :
    left.refinementFromStore? right initial = some verdict ↔
      ∃ (a : Denote inputType) (b : Denote rightType),
        left.seed? initial = some a ∧ right.seed? initial = some b ∧
        (verdict = true ↔ ∀ policy : Model.{0, 0} signature.traceSignature.toSignature,
          TraceInstitution.Sat policy (leftAdmission.refinementSentence rightAdmission a b)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Refinement.store_iff leftAdmission rightAdmission initial verdict

/-- The existing finite verdict decides validity over all jointly decoded
stores. The aggregate still reports an empty domain separately. -/
theorem OccurrenceAdmission.refinementOverCaptures_iff_valid [DecidableEq F] :
    (left.refinementOverCaptures right).verdict = some true ↔
      ∀ initial (a : Denote inputType) (b : Denote rightType),
        left.seed? initial = some a → right.seed? initial = some b →
        ∀ policy : Model.{0, 0} signature.traceSignature.toSignature,
          TraceInstitution.Sat policy (leftAdmission.refinementSentence rightAdmission a b) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Refinement.domain_iff leftAdmission rightAdmission

/-- The extracted representative yields both decoded packets. The same
trace separates the admitted runners and refutes their sentence. -/
theorem CaptureTraceWitness.refutes_occurrences
    {witness : CaptureTraceWitness V signature} (refutes : witness.Refutes left right) :
    ∃ (a : Denote inputType) (b : Denote rightType),
      left.seed? witness.initial = some a ∧ right.seed? witness.initial = some b ∧
      HandledTrace signature.traceModel.step () (left.observeOccurrences a) witness.trace ∧
      ¬ HandledTrace signature.traceModel.step () (right.observeOccurrences b) witness.trace ∧
      ¬ TraceInstitution.Sat signature.traceModel (leftAdmission.refinementSentence rightAdmission a b) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Refinement.witness_refutes leftAdmission rightAdmission refutes

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
