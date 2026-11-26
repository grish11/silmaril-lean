module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.RegisterRename.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Refinement.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.RegisterRename

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat (elaborate check)
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback (Provenance)
open Silmaril.SSA.LambdaRTL (CFG Val)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)
open Silmaril.Elgot.ITree (HandledTrace)
open Silmaril.Logic.ITree

variable {V W : Type 1} {F : Type} {inputType : PacketType}

private theorem operand_cast {m n m' n' p q r exits : Nat} {target : FiniteCFG F p q r}
    (blocks : m = m') (captures : n = n')
    (data : Σ flat : FiniteCFG F m exits n, Σ proof : Provenance flat target,
      StructuralSeed proof.seed inputType)
    (old : Fin n → V) (new : Fin n' → W) (offset : Nat) :
    let renamed := StructuralEntry.castReadback blocks captures data
    renamed.2.2.occurrenceOperand new offset = data.2.2.occurrenceOperand old offset := by
  subst m'
  subst n'
  rcases data with ⟨flat, proof, typed⟩
  change typed.occurrenceOperand new offset = typed.occurrenceOperand old offset
  have lengths {seed : Val (Fin n)} {ty : PacketType} (seedType : StructuralSeed seed ty) :
      (seedType.footprint new).length = (seedType.footprint old).length := by
    induction seedType <;> simp_all [StructuralSeed.footprint]
  generalize hseed : proof.seed = seed at typed ⊢
  clear hseed proof flat
  induction typed generalizing offset with
  | var | unit => rfl
  | pair left right ihl ihr =>
    simp only [StructuralSeed.occurrenceOperand, lengths left, ihl, ihr]

variable {K : Type 1} [DecidableEq V] [DecidableEq W] [DecidableEq K]
  {signature : PrimitiveSignature F} {source target : CFG V K F}
  {exits : List K} {fields : K → List V} {outputs : Fin exits.length → PacketType}
  {rightType : PacketType}
  (entry : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

theorem count_rename (names : V ↪ W) :
    entry.footprint.length = (entry.rename names).footprint.length := by
  rw [entry.footprint_rename, List.length_map]

theorem type_rename (names : V ↪ W) (i : Fin entry.footprint.length) :
    (entry.rename names).occurrenceContext.get (i.cast (count_rename entry names)) =
      entry.occurrenceContext.get i := by
  have bound : i.val < (entry.rename names).footprint.length := count_rename entry names ▸ i.isLt
  have indexed := congrArg (fun slots : List (W × PacketType) => slots[i.val]?.map Prod.snd)
    (entry.footprint_rename names)
  simp only [List.getElem?_eq_getElem bound, List.getElem?_map,
    List.getElem?_eq_getElem i.isLt, Option.map_some, Option.some.injEq] at indexed
  unfold StructuralEntry.occurrenceContext
  rw [BoundCtx.get_ofFin, BoundCtx.get_ofFin]
  exact indexed

theorem graph_rename (names : V ↪ W) :
    (entry.rename names).occurrenceGraph = entry.occurrenceGraph := by
  have operand : (entry.rename names).occurrenceOperand = entry.occurrenceOperand :=
    operand_cast _ _ ⟨entry.flat, entry.provenance, entry.typedSeed⟩
      (fun i => entry.names[i.val]) (fun i => (entry.names.map names)[i.val]) 0
  exact congrArg (fun arg => { entry.program.compile 0 with
    entry := .term (.br (⟨entry.program.entry 0⟩ : entry.program.Address) arg) }) operand

theorem store_rename (names : V ↪ W) (packet : Denote inputType) :
    (entry.rename names).occurrenceStore packet = entry.occurrenceStore packet := by
  funext reg
  simp only [StructuralEntry.occurrenceStore, entry.assignment_rename, List.getElem?_map]
  cases (entry.assignment packet)[reg.down]? <;> rfl

private def checkedErasure {L : Type 1} [DecidableEq L] {n : Nat}
    (signature : PrimitiveSignature F) (g : CFG Register L F) (exits : List L) (names : Fin n → Register)
    (context : BoundCtx PacketType n) (internal : Fin g.blocks.length → PacketType)
    (external : Fin exits.length → PacketType) : Option (LambdaSSA.Region F) :=
  letI := signature.typing
  ((elaborate g exits names).filter
    (fun code => check code context internal external)).map FiniteCFG.erase

private theorem admission_view :
    entry.admitOccurrences.map (fun admitted => admitted.code.erase) =
      checkedErasure signature entry.occurrenceGraph entry.program.exits entry.occurrenceNames
        entry.occurrenceContext entry.entry.blocks entry.entry.exits := by
  unfold StructuralEntry.admitOccurrences checkedErasure
  split
  · simp_all
  · split <;> simp_all

private theorem check_congr {L : Type 1} [DecidableEq L] {n m : Nat}
    (signature : PrimitiveSignature F) {g g' : CFG Register L F} (graph : g' = g)
    (exits : List L) (external : Fin exits.length → PacketType) (count : n = m)
    (names : Fin n → Register) (names' : Fin m → Register)
    (context : BoundCtx PacketType n) (context' : BoundCtx PacketType m)
    (internal : Fin g.blocks.length → PacketType) (internal' : Fin g'.blocks.length → PacketType)
    (namesEq : ∀ i, names' (i.cast count) = names i)
    (typesEq : ∀ i, context'.get (i.cast count) = context.get i)
    (internalEq : HEq internal' internal) :
    checkedErasure signature g' exits names' context' internal' external =
      checkedErasure signature g exits names context internal external := by
  subst g'
  subst m
  have namesEqual : names' = names := funext namesEq
  have ctxEqual : context' = context := (BoundCtx.finEquiv _ _).injective (funext typesEq)
  rw [namesEqual, ctxEqual, eq_of_heq internalEq]

theorem admission_rename (names : V ↪ W) :
    (entry.rename names).admitOccurrences.map (fun admitted => admitted.code.erase) =
      entry.admitOccurrences.map (fun admitted => admitted.code.erase) := by
  rw [admission_view, admission_view]
  exact check_congr signature (graph_rename entry names) entry.program.exits entry.entry.exits
    (count_rename entry names) entry.occurrenceNames (entry.rename names).occurrenceNames
    entry.occurrenceContext (entry.rename names).occurrenceContext entry.entry.blocks (entry.rename names).entry.blocks
    (fun _ => rfl) (type_rename entry names) HEq.rfl

theorem observe_rename (names : V ↪ W) (packet : Denote inputType) :
    (entry.rename names).observeOccurrences packet = entry.observeOccurrences packet := by
  unfold StructuralEntry.observeOccurrences
  rw [graph_rename entry names, store_rename entry names packet]
  rfl

theorem decoded_observe_rename (names : V ≃ W) (initial : V → Value Atom) :
    ((entry.rename names.toEmbedding).seed? (renameStore names initial)).map
        (entry.rename names.toEmbedding).observeOccurrences =
      (entry.seed? initial).map entry.observeOccurrences := by
  rw [entry.seed?_rename]
  exact congrArg (fun observe => (entry.seed? initial).map observe)
    (funext (observe_rename entry names.toEmbedding))

theorem sentence_rename (names : V ↪ W)
    (leftAdmission : OccurrenceAdmission entry) (rightAdmission : OccurrenceAdmission right)
    (renamedLeft : OccurrenceAdmission (entry.rename names))
    (renamedRight : OccurrenceAdmission (right.rename names))
    (a : Denote inputType) (b : Denote rightType) :
    renamedLeft.refinementSentence renamedRight a b = leftAdmission.refinementSentence rightAdmission a b := by
  unfold OccurrenceAdmission.refinementSentence
  erw [observe_rename entry names a, observe_rename right names b]

theorem witness_rename (names : V ≃ W)
    (leftAdmission : OccurrenceAdmission entry) (rightAdmission : OccurrenceAdmission right)
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
      ¬ TraceInstitution.Sat signature.traceModel (renamedLeft.refinementSentence renamedRight a b) := by
  obtain ⟨a, b, ha, hb, seen, absent, rejected⟩ :=
    witness.refutes_occurrences leftAdmission rightAdmission refutes
  refine ⟨a, b, (entry.seed?_rename names witness.initial).trans ha,
    (right.seed?_rename names witness.initial).trans hb, ?_⟩
  erw [observe_rename entry names.toEmbedding a, observe_rename right names.toEmbedding b,
    sentence_rename entry right names.toEmbedding leftAdmission rightAdmission renamedLeft renamedRight a b]
  exact ⟨seen, absent, rejected⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.RegisterRename
