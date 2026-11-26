module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.RegisterRename.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Refinement.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.RegisterRename

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip (renameGraph)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.Elgot.ITree (HandledTrace)
open Silmaril.Logic.ITree

variable {V W K : Type 1} [DecidableEq V] [DecidableEq W] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F}
  {exits : List K} {fields : K → List V} {outputs : Fin exits.length → PacketType}
  {inputType rightType : PacketType}
  (entry : StructuralEntry signature source exits fields inputType outputs)

theorem StructuralEntry.occurrenceCount_rename (names : V ↪ W) :
    entry.footprint.length = (entry.rename names).footprint.length :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.RegisterRename.count_rename
    entry names

/-- Each numbered occurrence retains its exact type, in the same position. -/
theorem StructuralEntry.occurrenceType_rename (names : V ↪ W) (i : Fin entry.footprint.length) :
    (entry.rename names).occurrenceContext.get (i.cast (entry.occurrenceCount_rename names)) =
      entry.occurrenceContext.get i :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.RegisterRename.type_rename
    entry names i

/-- The occurrence builder emits the same named graph after transporting the
structural certificate. Its registers belong to the numbered adapter. -/
theorem StructuralEntry.occurrenceGraph_rename (names : V ↪ W) :
    (entry.rename names).occurrenceGraph = entry.occurrenceGraph :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.RegisterRename.graph_rename
    entry names

/-- The typed seed supplies the same values to the numbered adapter store. -/
theorem StructuralEntry.occurrenceStore_rename (names : V ↪ W) (packet : Denote inputType) :
    (entry.rename names).occurrenceStore packet = entry.occurrenceStore packet :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.RegisterRename.store_rename
    entry names packet

/-- Exact admission agrees after erasing certificates. A successful check
returns the same flat code after its scope indices are erased. -/
theorem StructuralEntry.admitOccurrences_rename (names : V ↪ W) :
    (entry.rename names).admitOccurrences.map (fun admitted => admitted.code.erase) =
      entry.admitOccurrences.map (fun admitted => admitted.code.erase) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.RegisterRename.admission_rename
    entry names

theorem StructuralEntry.admitOccurrences_isSome_rename (names : V ↪ W) :
    (entry.rename names).admitOccurrences.isSome = entry.admitOccurrences.isSome := by
  simpa only [Option.isSome_map] using congrArg Option.isSome (entry.admitOccurrences_rename names)

/-- The actual named SSA runs give the same ordered exit and payload tree. -/
theorem StructuralEntry.observeOccurrences_rename (names : V ↪ W) (packet : Denote inputType) :
    (entry.rename names).observeOccurrences packet = entry.observeOccurrences packet :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.RegisterRename.observe_rename
    entry names packet

/-- Decode the transported store and run the generated occurrence entry.
The resulting observation agrees, including failure to decode. -/
theorem StructuralEntry.decodedOccurrences_rename (names : V ≃ W) (initial : V → Value Atom) :
    ((entry.rename names.toEmbedding).seed? (renameStore names initial)).map
        (entry.rename names.toEmbedding).observeOccurrences =
      (entry.seed? initial).map entry.observeOccurrences :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.RegisterRename.decoded_observe_rename
    entry names initial

/-- The renamed original RTL and the rebuilt occurrence entry agree at the
transported store, with the same ordered exits and corresponding live-outs. -/
theorem StructuralEntry.observeRaw_eq_renamedOccurrences (names : V ≃ W) (initial : V → Value Atom)
    (packet : Denote inputType) (checked : entry.seed? initial = some packet) :
    LiveOut.observeRaw signature.primitive exits (fun k => (fields k).map names.toEmbedding)
        (renameGraph names.toEmbedding source) (renameStore names initial) =
      (entry.rename names.toEmbedding).observeOccurrences packet :=
  (entry.observe_rename names initial).trans <|
    (entry.observeRaw_eq_occurrences initial packet checked).trans (entry.observeOccurrences_rename _ _).symm

variable {entry} {right : StructuralEntry signature target exits fields rightType outputs}

/-- Use the same handled-trace sentence on both pairs of exact-admitted runners. -/
theorem OccurrenceAdmission.refinementSentence_rename
    (leftAdmission : OccurrenceAdmission entry) (rightAdmission : OccurrenceAdmission right) (names : V ↪ W)
    (renamedLeft : OccurrenceAdmission (entry.rename names))
    (renamedRight : OccurrenceAdmission (right.rename names))
    (a : Denote inputType) (b : Denote rightType) :
    renamedLeft.refinementSentence renamedRight a b = leftAdmission.refinementSentence rightAdmission a b :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.RegisterRename.sentence_rename
    entry right names leftAdmission rightAdmission renamedLeft renamedRight a b

/-- Transport the witness store along the register bijection. Both seeds
still decode and the same trace refutes the renamed admitted runners. -/
theorem CaptureTraceWitness.refutes_renamed_occurrences
    (leftAdmission : OccurrenceAdmission entry) (rightAdmission : OccurrenceAdmission right) (names : V ≃ W)
    (renamedLeft : OccurrenceAdmission (entry.rename names.toEmbedding))
    (renamedRight : OccurrenceAdmission (right.rename names.toEmbedding))
    {witness : CaptureTraceWitness V signature} (refutes : witness.Refutes entry right) :
    ∃ (a : Denote inputType) (b : Denote rightType),
      (entry.rename names.toEmbedding).seed? (witness.rename names).initial = some a ∧
      (right.rename names.toEmbedding).seed? (witness.rename names).initial = some b ∧
      HandledTrace signature.traceModel.step ()
        ((entry.rename names.toEmbedding).observeOccurrences a) (witness.rename names).trace ∧
      ¬ HandledTrace signature.traceModel.step ()
        ((right.rename names.toEmbedding).observeOccurrences b) (witness.rename names).trace ∧
      ¬ TraceInstitution.Sat signature.traceModel (renamedLeft.refinementSentence renamedRight a b) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.RegisterRename.witness_rename
    entry right names leftAdmission rightAdmission renamedLeft renamedRight refutes

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
