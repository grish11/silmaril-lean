module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.NamedSSA.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Institution.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.NamedSSA

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.Elgot.ITree (HandledTrace)
open Silmaril.Logic.ITree
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

/-- The actual versioned named runner computes the original RTL observation,
including the ordered exit and selected live-outs, from the version-zero store. -/
theorem StructuralEntry.observeVersioned_eq (initial : V → Value Atom) :
    left.observeVersioned initial = LiveOut.observeRaw signature.primitive exits fields source initial :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.NamedSSA.observe_eq left initial

/-- At a successfully decoded seed, the versioned original and the admitted
public named SSA runner give the same tagged observation. Each program
uses its own public packet type. -/
theorem StructuralEntry.observeVersioned_eq_public (initial : V → Value Atom) (packet : Denote inputType)
    (checked : left.seed? initial = some packet) :
    left.observeVersioned initial =
      (left.program.observe 0 packet >>= fun result => pure (FiniteCFG.packedTreeOutput result)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.NamedSSA.observe_public left initial packet checked

/-- Satisfaction in each existing handled-trace model transports by equality
of sentences at the common source store. -/
theorem StructuralEntry.versionedRefinementSentence_eq (initial : V → Value Atom) :
    left.versionedRefinementSentence right initial = left.refinementSentenceAt right initial :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.NamedSSA.sentence_eq left right initial

/-- The finite RTL verdict is exactly validity of the original versioned SSA
comparison at every jointly decoded store, under all shared reply policies. -/
theorem StructuralEntry.refinementOverCaptures_iff_valid_versioned [DecidableEq F] :
    (left.refinementOverCaptures right).verdict = some true ↔
      ∀ initial (a : Denote inputType) (b : Denote rightType),
        left.seed? initial = some a → right.seed? initial = some b →
        ∀ policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature,
          TraceInstitution.Sat policy (left.versionedRefinementSentence right initial) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.NamedSSA.refinement_iff left right

/-- The original directed trace still separates the two actual versioned
SSA runners and refutes their sentence in the all-replies model. -/
theorem CaptureTraceWitness.refutes_versioned {witness : CaptureTraceWitness V signature} (refutes : witness.Refutes left right) :
    HandledTrace signature.traceModel.step () (left.observeVersioned witness.initial) witness.trace ∧
      ¬ HandledTrace signature.traceModel.step () (right.observeVersioned witness.initial) witness.trace ∧
      ¬ TraceInstitution.Sat signature.traceModel (left.versionedRefinementSentence right witness.initial) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.NamedSSA.witness_refutes left right refutes

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
