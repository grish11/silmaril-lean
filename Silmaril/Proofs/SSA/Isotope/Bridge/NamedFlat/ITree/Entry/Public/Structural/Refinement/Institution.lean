module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Institution.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Witness.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Reindex.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Institution

open CategoryTheory
open Silmaril.Elgot.ITree (HasTrace TraceSignature)
open Silmaril.Logic.ITree
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)
  {Target : TraceSignature.{0}} (f : signature.traceSignature ⟶ Target) (ambient : Env Atom)

theorem sentence_reindexed (initial : V → Value Atom) (a : Denote inputType) (b : Denote rightType)
    (checkedLeft : left.evalSeed initial = PacketType.encode inputType a)
    (checkedRight : right.evalSeed initial = PacketType.encode rightType b) :
    (left.refinementSentenceAt right initial).translate f =
      left.packedRefinementSentenceReindexed right f ambient a b := by
  rw [StructuralEntry.packedRefinementSentenceReindexed, ← left.entry.refinementSentence_reindexed right.entry f]
  congr 1
  unfold StructuralEntry.refinementSentenceAt Program.PackedEntry.refinementSentence
  rw [left.observe_eq initial a ambient checkedLeft, right.observe_eq initial b ambient checkedRight]
  rfl

theorem domain_iff_valid [DecidableEq F] :
    (left.refinementOverCaptures right).verdict = some true ↔
      ∀ initial (a : Denote inputType) (b : Denote rightType),
        left.evalSeed initial = PacketType.encode inputType a →
        right.evalSeed initial = PacketType.encode rightType b →
        ∀ policy : Silmaril.Logic.ITree.Model.{0, 0} Target.toSignature,
          TraceInstitution.Sat policy (left.packedRefinementSentenceReindexed right f ambient a b) := by
  have pointwise (initial : V → Value Atom) (a : Denote inputType) (b : Denote rightType)
      (ha : left.evalSeed initial = PacketType.encode inputType a)
      (hb : right.evalSeed initial = PacketType.encode rightType b) :
      (∀ policy : Silmaril.Logic.ITree.Model.{0, 0} Target.toSignature,
        TraceInstitution.Sat policy (left.packedRefinementSentenceReindexed right f ambient a b)) ↔
      (∀ policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature,
        TraceInstitution.Sat policy (left.refinementSentenceAt right initial)) := by
    rw [← sentence_reindexed left right f ambient initial a b ha hb, StructuralEntry.refinementSentenceAt,
      TraceInstitution.translate_hasTrace, TraceInstitution.valid_hasTrace_iff,
      TraceInstitution.valid_hasTrace_iff, f.traceLE_iff]
  simp only [left.refinementOverCaptures_eq_some_iff right true, eq_self, true_iff]
  constructor
  · intro valid initial a b ha hb
    apply (pointwise initial a b ha hb).mpr
    intro policy x hx trace seen
    exact (valid initial ⟨a, ha⟩ ⟨b, hb⟩ policy x hx trace seen).1
  · intro valid initial ⟨a, ha⟩ ⟨b, hb⟩ policy x hx trace seen
    exact ⟨(pointwise initial a b ha hb).mp (valid initial a b ha hb) policy x hx trace seen, seen.2⟩

theorem witness_reindexed {witness : CaptureTraceWitness V signature} (refutes : witness.Refutes left right)
    (a : Denote inputType) (b : Denote rightType)
    (checkedLeft : left.evalSeed witness.initial = PacketType.encode inputType a)
    (checkedRight : right.evalSeed witness.initial = PacketType.encode rightType b) :
    HasTrace (left.entry.observeReindexed f ambient (packetRecord a)) (f.trace witness.trace) ∧
      ¬ HasTrace (right.entry.observeReindexed f ambient (packetRecord b)) (f.trace witness.trace) := by
  rw [left.entry.observe_reindexed, right.entry.observe_reindexed,
    left.observe_eq witness.initial a ambient checkedLeft, right.observe_eq witness.initial b ambient checkedRight]
  refine ⟨(f.hasTrace_image _ _).mpr ⟨witness.trace, (signature.handledTrace_iff _ _).mp refutes.2.1, rfl⟩, ?_⟩
  intro has
  obtain ⟨trace, observed, same⟩ := (f.hasTrace_image _ _).mp has
  exact refutes.2.2 ((signature.handledTrace_iff _ _).mpr (f.trace_injective same ▸ observed))

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Institution
