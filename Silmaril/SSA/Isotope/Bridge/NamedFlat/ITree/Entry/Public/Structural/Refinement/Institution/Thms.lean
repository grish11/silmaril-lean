module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Institution.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Witness.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Reindex.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Institution

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open CategoryTheory
open Silmaril.Elgot.ITree (HasTrace TraceSignature)
open Silmaril.Logic.ITree
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA.Semantics (Env)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)
  {Target : TraceSignature.{0}} (f : signature.traceSignature ⟶ Target) (ambient : Env Atom)

/-- The existing signature action takes the named sentence to the
comparison of the actual packed runs at both checked seeds. -/
theorem StructuralEntry.refinementSentence_reindexed (initial : V → Value Atom) (a : Denote inputType) (b : Denote rightType)
    (checkedLeft : left.evalSeed initial = PacketType.encode inputType a)
    (checkedRight : right.evalSeed initial = PacketType.encode rightType b) :
    (left.refinementSentenceAt right initial).translate f =
      left.packedRefinementSentenceReindexed right f ambient a b :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Institution.sentence_reindexed
    left right f ambient initial a b checkedLeft checkedRight

/-- Satisfaction of the actual packed comparison in the target handler
uses the existing reduct on the original named comparison. -/
theorem StructuralEntry.sat_reindexed_iff (initial : V → Value Atom)
    (a : Denote inputType) (b : Denote rightType)
    (checkedLeft : left.evalSeed initial = PacketType.encode inputType a)
    (checkedRight : right.evalSeed initial = PacketType.encode rightType b)
    (policy : Silmaril.Logic.ITree.Model.{0, 0} Target.toSignature) :
    TraceInstitution.Sat policy (left.packedRefinementSentenceReindexed right f ambient a b) ↔
      TraceInstitution.Sat (policy.reduct f.hom) (left.refinementSentenceAt right initial) := by
  rw [← left.refinementSentence_reindexed right f ambient initial a b checkedLeft checkedRight]
  exact TraceInstitution.satisfaction f policy _

/-- The original finite verdict decides validity of the translated packed
sentences over every jointly typed store and shared reply policy. -/
theorem StructuralEntry.refinementOverCaptures_iff_valid_reindexed [DecidableEq F] :
    (left.refinementOverCaptures right).verdict = some true ↔
      ∀ initial (a : Denote inputType) (b : Denote rightType),
        left.evalSeed initial = PacketType.encode inputType a →
        right.evalSeed initial = PacketType.encode rightType b →
        ∀ policy : Silmaril.Logic.ITree.Model.{0, 0} Target.toSignature,
          TraceInstitution.Sat policy (left.packedRefinementSentenceReindexed right f ambient a b) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Institution.domain_iff_valid
    left right f ambient

/-- The same directed witness transports under typed event-key relabelling.
The terminal observation retains the ordered exit tag and live-out payload. -/
theorem CaptureTraceWitness.distinguishes_reindexed {witness : CaptureTraceWitness V signature} (refutes : witness.Refutes left right)
    (a : Denote inputType) (b : Denote rightType)
    (checkedLeft : left.evalSeed witness.initial = PacketType.encode inputType a)
    (checkedRight : right.evalSeed witness.initial = PacketType.encode rightType b) :
    HasTrace (left.entry.observeReindexed f ambient (packetRecord a)) (f.trace witness.trace) ∧
      ¬ HasTrace (right.entry.observeReindexed f ambient (packetRecord b)) (f.trace witness.trace) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Institution.witness_reindexed
    left right f ambient refutes a b checkedLeft checkedRight

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
