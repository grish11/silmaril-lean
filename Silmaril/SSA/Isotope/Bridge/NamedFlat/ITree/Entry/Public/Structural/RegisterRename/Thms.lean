module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.RegisterRename.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Institution.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.RegisterRename

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open CategoryTheory
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip (renameGraph)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.Elgot.ITree (TraceSignature)

variable {V W K : Type 1} [DecidableEq V] [DecidableEq W] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F}
  {exits : List K} {fields : K → List V} {outputs : Fin exits.length → PacketType}
  {inputType rightType : PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

/-- Every typed occurrence is renamed in place, including repetitions. -/
theorem StructuralEntry.footprint_rename (names : V ↪ W) :
    (left.rename names).footprint = left.footprint.map (Prod.map names id) :=
  (Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.RegisterRename.seeds_rename left names).1

/-- The same structural value is read from corresponding capture slots. -/
theorem StructuralEntry.evalSeed_rename (names : V ↪ W) (initial : V → Value Atom) (other : W → Value Atom)
    (agrees : ∀ x, other (names x) = initial x) : (left.rename names).evalSeed other = left.evalSeed initial :=
  (Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.RegisterRename.seeds_rename left names).2.2
    initial other agrees

/-- Successful and failed decoding are both preserved by store transport. -/
theorem StructuralEntry.seed?_rename (names : V ≃ W) (initial : V → Value Atom) :
    (left.rename names.toEmbedding).seed? (renameStore names initial) = left.seed? initial :=
  congrArg (decodeSeed? inputType) <| left.evalSeed_rename _ _ _ fun x =>
    congrArg initial (names.symm_apply_apply x)

include left in
/-- The original and renamed named runners have the same whole weak tree
at corresponding stores, including the numbered exit and ordered live-outs. -/
theorem StructuralEntry.observe_rename (names : V ≃ W) (initial : V → Value Atom) :
    LiveOut.observeRaw signature.primitive exits (fun k => (fields k).map names.toEmbedding) (renameGraph names.toEmbedding source)
        (renameStore names initial) =
      LiveOut.observeRaw signature.primitive exits fields source initial :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.RegisterRename.observe_rename
    left names initial

/-- The enumerated joint stores are transported in order. Shared registers
and repeated capture occurrences still have a single raw value. -/
theorem StructuralEntry.jointStores_rename (names : V ≃ W) :
    (left.rename names.toEmbedding).jointStores (right.rename names.toEmbedding) =
      (left.jointStores right).map (renameStore names) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.RegisterRename.jointStores_rename
    left right names

/-- The same exact typed trace refutes the comparison at the transported
representative store if and only if it refutes the original comparison. -/
theorem CaptureTraceWitness.refutes_rename_iff (witness : CaptureTraceWitness V signature) (names : V ≃ W) :
    (witness.rename names).Refutes (left.rename names.toEmbedding) (right.rename names.toEmbedding) ↔
      witness.Refutes left right :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.RegisterRename.witness_refutes_iff
    left right names witness

/-- Register renaming preserves the original named sentence at corresponding
stores, for use with the existing event-signature action and reduct. -/
theorem StructuralEntry.refinementSentenceAt_rename (names : V ≃ W) (initial : V → Value Atom) :
    (left.rename names.toEmbedding).refinementSentenceAt (right.rename names.toEmbedding)
      (renameStore names initial) = left.refinementSentenceAt right initial :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.RegisterRename.sentence_rename
    left right names initial

/-- Compose register renaming at the two checked starts with faithful
event relabelling and the existing target-policy reduct. -/
theorem StructuralEntry.sat_reindexed_rename_iff (names : V ≃ W) (initial : V → Value Atom)
    (a : Denote inputType) (b : Denote rightType)
    (ha : left.evalSeed initial = PacketType.encode inputType a)
    (hb : right.evalSeed initial = PacketType.encode rightType b)
    {Target : TraceSignature.{0}} (f : signature.traceSignature ⟶ Target) (ambient : LambdaSSA.Semantics.Env Atom)
    (policy : Silmaril.Logic.ITree.Model.{0, 0} Target.toSignature) :
    Silmaril.Logic.ITree.TraceInstitution.Sat policy
      ((left.rename names.toEmbedding).packedRefinementSentenceReindexed
        (right.rename names.toEmbedding) f ambient a b) ↔
    Silmaril.Logic.ITree.TraceInstitution.Sat (policy.reduct f.hom)
      (left.refinementSentenceAt right initial) :=
  left.sat_reindexed_iff right f ambient initial a b ha hb policy

variable [DecidableEq F]

/-- The pointwise decision agrees at the transported store, including when
either seed fails to decode. -/
theorem StructuralEntry.refinementFromStore?_rename (names : V ≃ W) (initial : V → Value Atom) :
    (left.rename names.toEmbedding).refinementFromStore? (right.rename names.toEmbedding)
      (renameStore names initial) = left.refinementFromStore? right initial :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.RegisterRename.store_verdict_rename
    left right names initial

/-- The domain flag and the aggregate decision agree after register renaming. -/
theorem StructuralEntry.refinementOverCaptures_rename (names : V ≃ W) :
    (left.rename names.toEmbedding).refinementOverCaptures (right.rename names.toEmbedding) =
      left.refinementOverCaptures right :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.RegisterRename.domain_verdict_rename
    left right names

/-- The executable extractor returns the same trace and the corresponding
named store, or fails on both sides. -/
theorem StructuralEntry.explainRefinementOverCaptures?_rename (names : V ≃ W) :
    (left.rename names.toEmbedding).explainRefinementOverCaptures? (right.rename names.toEmbedding) =
      (left.explainRefinementOverCaptures? right).map (fun w => w.rename names) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.RegisterRename.explain_rename
    left right names

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
