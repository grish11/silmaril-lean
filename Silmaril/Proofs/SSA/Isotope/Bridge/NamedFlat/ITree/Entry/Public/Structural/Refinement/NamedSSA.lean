module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.NamedSSA.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Institution.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.NamedSSA

open CategoryTheory
open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat (treeModel)
open Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
open Silmaril.Elgot.ITree (HandledTrace HasTrace)
open Silmaril.Logic.ITree
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

theorem observe_eq (initial : V → Value Atom) :
    left.observeVersioned initial = LiveOut.observeRaw signature.primitive exits fields source initial := by
  unfold StructuralEntry.observeVersioned StructuralEntry.versioned
  rw [observe_version]
  unfold rtlObserve
  rw [CFG.Cyclic.LiveOut.run_project]
  simp only [LiveOut.observeRaw, bind_map_left]

theorem observe_public (initial : V → Value Atom) (packet : Denote inputType)
    (checked : left.seed? initial = some packet) :
    left.observeVersioned initial =
      (left.program.observe 0 packet >>= fun result => pure (FiniteCFG.packedTreeOutput result)) := by
  let ambient : Env Atom := fun _ => .unit
  have encoded := (decodeSeed?_eq_some_iff inputType _ packet).mp checked
  exact (observe_eq left initial).trans ((left.observe_eq initial packet ambient encoded).symm.trans
    (left.entry.observe_eq packet ambient (packetRecord packet)
      (recordAgrees_packetRecord left.entry left.publicCaptures packet)))

theorem sentence_eq (initial : V → Value Atom) :
    left.versionedRefinementSentence right initial = left.refinementSentenceAt right initial := by
  unfold StructuralEntry.versionedRefinementSentence StructuralEntry.refinementSentenceAt
  erw [observe_eq left initial, observe_eq right initial]
  rfl

theorem refinement_iff [DecidableEq F] :
    (left.refinementOverCaptures right).verdict = some true ↔
      ∀ initial (a : Denote inputType) (b : Denote rightType),
        left.seed? initial = some a → right.seed? initial = some b →
        ∀ policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature,
          TraceInstitution.Sat policy (left.versionedRefinementSentence right initial) := by
  let f := 𝟙 signature.traceSignature
  let ambient : Env Atom := fun _ => .unit
  have commute (initial : V → Value Atom) (a : Denote inputType) (b : Denote rightType)
      (ha : left.evalSeed initial = PacketType.encode inputType a)
      (hb : right.evalSeed initial = PacketType.encode rightType b) :
      left.packedRefinementSentenceReindexed right f ambient a b =
        left.versionedRefinementSentence right initial := by
    rw [← left.refinementSentence_reindexed right f ambient initial a b ha hb, sentence_eq left right initial]
    exact TraceInstitution.Sentence.translate_id _
  refine (left.refinementOverCaptures_iff_valid_reindexed right f ambient).trans ?_
  simp only [StructuralEntry.seed?, decodeSeed?_eq_some_iff]
  constructor <;> intro valid initial a b ha hb policy
  · rw [← commute initial a b ha hb]
    exact valid initial a b ha hb policy
  · rw [commute initial a b ha hb]
    exact valid initial a b ha hb policy

theorem witness_refutes {witness : CaptureTraceWitness V signature} (refutes : witness.Refutes left right) :
    HandledTrace signature.traceModel.step () (left.observeVersioned witness.initial) witness.trace ∧
      ¬ HandledTrace signature.traceModel.step () (right.observeVersioned witness.initial) witness.trace ∧
      ¬ TraceInstitution.Sat signature.traceModel (left.versionedRefinementSentence right witness.initial) := by
  have seen : HandledTrace signature.traceModel.step () (left.observeVersioned witness.initial) witness.trace :=
    (observe_eq left witness.initial).symm ▸ refutes.2.1
  have absent : ¬ HandledTrace signature.traceModel.step () (right.observeVersioned witness.initial) witness.trace :=
    (observe_eq right witness.initial).symm ▸ refutes.2.2
  refine ⟨seen, absent, fun sat => absent ?_⟩
  exact (signature.handledTrace_iff _ _).mpr (sat () trivial witness.trace seen)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.NamedSSA
