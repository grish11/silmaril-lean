module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.RegisterRename.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Institution.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.RegisterRename

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut (observeRaw)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback (Provenance packetValue)
open Silmaril.SSA.LambdaRTL (CFG upd obs)
open Silmaril.Isotope.Bridge.NamedFlat (treeModel treeExitNumber)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip (renameGraph)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)
open Silmaril.Elgot.ITree (HasTrace)

variable {V W K : Type 1} {F : Type} {inputType : PacketType}

private theorem readback_rename {m n m' n' p q r exits : Nat} {target : FiniteCFG F p q r}
    (names : V ↪ W) (blocks : m = m') (captures : n = n')
    (data : Σ flat : FiniteCFG F m exits n, Σ proof : Provenance flat target,
      StructuralSeed proof.seed inputType)
    (old : Fin n → V) (new : Fin n' → W) (aligned : ∀ i, new (i.cast captures) = names (old i)) :
    let renamed := StructuralEntry.castReadback blocks captures data
    renamed.2.2.footprint new = (data.2.2.footprint old).map (Prod.map names id) ∧
      (∀ packet, renamed.2.2.assignment new packet =
        (data.2.2.assignment old packet).map (Prod.map names id)) ∧
      (∀ (initial : V → Value Atom) (other : W → Value Atom),
        (∀ x, other (names x) = initial x) →
        packetValue (StructuralSeed.captureEnv new other) renamed.2.1.seed =
          packetValue (StructuralSeed.captureEnv old initial) data.2.1.seed) := by
  subst m'
  subst n'
  rcases data with ⟨flat, proof, typed⟩
  change (∀ i, new i = names (old i)) at aligned
  change typed.footprint new = (typed.footprint old).map (Prod.map names id) ∧
    (∀ packet, typed.assignment new packet = (typed.assignment old packet).map (Prod.map names id)) ∧
    (∀ (initial : V → Value Atom) (other : W → Value Atom), (∀ x, other (names x) = initial x) →
      packetValue (StructuralSeed.captureEnv new other) proof.seed =
        packetValue (StructuralSeed.captureEnv old initial) proof.seed)
  generalize seedEq : proof.seed = seed at typed ⊢
  clear seedEq proof flat
  induction typed with
  | var slot ty =>
    simp [StructuralSeed.footprint, StructuralSeed.assignment, packetValue, StructuralSeed.captureEnv,
      slot.isLt, aligned]
    intro initial other agree
    exact agree (old slot)
  | unit => simp [StructuralSeed.footprint, StructuralSeed.assignment, packetValue]
  | pair left right l r =>
    refine ⟨by simp [StructuralSeed.footprint, l.1, r.1], ?_, ?_⟩
    · rintro ⟨a, b⟩
      simp [StructuralSeed.assignment, l.2.1 a, r.2.1 b]
    · intro initial other agree
      simp [packetValue, l.2.2 initial other agree, r.2.2 initial other agree]

variable [DecidableEq V] [DecidableEq W] [DecidableEq K]
  {signature : PrimitiveSignature F} {source target : CFG V K F}
  {exits : List K} {fields : K → List V} {outputs : Fin exits.length → PacketType}
  {rightType : PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

theorem seeds_rename (names : V ↪ W) :
    (left.rename names).footprint = left.footprint.map (Prod.map names id) ∧
      (∀ packet, (left.rename names).assignment packet = (left.assignment packet).map (Prod.map names id)) ∧
      (∀ (initial : V → Value Atom) (other : W → Value Atom),
        (∀ x, other (names x) = initial x) → (left.rename names).evalSeed other = left.evalSeed initial) := by
  exact readback_rename names _ _ ⟨left.flat, left.provenance, left.typedSeed⟩
    (fun i => left.names[i.val]) (fun i => (left.names.map names)[i.val])
    (fun _ => List.getElem_map ..)

include left in
theorem observe_rename (names : V ≃ W) (initial : V → Value Atom) :
    observeRaw signature.primitive exits (fun k => (fields k).map names.toEmbedding)
        (renameGraph names.toEmbedding source) (renameStore names initial) =
      observeRaw signature.primitive exits fields source initial := by
  let model := treeModel signature.primitive
  let output := fun (p : K × Value Atom) => FiniteCFG.packedTreeOutput (treeExitNumber exits p)
  have runs := CFG.Cyclic.RegisterRename.run_attach_obs_rename names.toEmbedding model
    fields source left.closed initial (renameStore names initial)
    (fun x => congrArg initial (names.symm_apply_apply x))
  have outputs := congrArg (fun t => output <$> t) runs
  simp only [CFG.Cyclic.LiveOut.run_project, Functor.map_map] at outputs
  unfold observeRaw
  simpa only [map_eq_pure_bind, Function.comp_def, model, output] using outputs

private theorem assignmentStore_rename (names : V ↪ W) (assignment : List (V × Value Atom)) (x : V) :
    StructuralSeed.assignmentStore (assignment.map (Prod.map names id)) (names x) =
      StructuralSeed.assignmentStore assignment x := by
  induction assignment with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨register, value⟩ := head
    simp [StructuralSeed.assignmentStore, upd, names.injective.eq_iff, ih]

theorem jointStores_rename (names : V ≃ W) :
    (left.rename names.toEmbedding).jointStores (right.rename names.toEmbedding) =
      (left.jointStores right).map (renameStore names) := by
  let renameAssignment : List (V × Value Atom) → List (W × Value Atom) := List.map (Prod.map names.toEmbedding id)
  have keepsConsistency (assignment : List (V × Value Atom)) :
      (renameAssignment assignment).all (fun pair =>
        decide (StructuralSeed.assignmentStore (renameAssignment assignment) pair.1 = pair.2)) =
      assignment.all (fun pair =>
        decide (StructuralSeed.assignmentStore assignment pair.1 = pair.2)) := by
    rw [List.all_map]
    apply congrArg (fun test => assignment.all test)
    funext pair
    rcases pair with ⟨name, value⟩
    simp only [renameAssignment, Function.comp_apply, Prod.map_apply, id_eq, assignmentStore_rename]
  have assignments :
      (left.rename names.toEmbedding).jointAssignments (right.rename names.toEmbedding) =
        (left.jointAssignments right).map renameAssignment := by
    unfold StructuralEntry.jointAssignments
    rw [List.map_filterMap]
    apply congrArg (fun choose => (inputType.enumerate.product rightType.enumerate).filterMap choose)
    funext packets
    rcases packets with ⟨a, b⟩
    simp only [(seeds_rename left names.toEmbedding).2.1 a, (seeds_rename right names.toEmbedding).2.1 b]
    simp only [← List.map_append]
    change (if (renameAssignment (left.assignment a ++ right.assignment b)).all _ then
      some (renameAssignment (left.assignment a ++ right.assignment b)) else none) = _
    rw [keepsConsistency]
    split <;> rfl
  unfold StructuralEntry.jointStores
  rw [assignments, List.map_map, List.map_map]
  apply congrArg (fun f => (left.jointAssignments right).map f)
  funext assignment key
  obtain ⟨x, rfl⟩ := names.surjective key
  simpa only [Function.comp_apply, renameAssignment, renameStore, names.symm_apply_apply, Equiv.coe_toEmbedding] using
    assignmentStore_rename names.toEmbedding assignment x

theorem witness_refutes_iff (names : V ≃ W) (witness : CaptureTraceWitness V signature) :
    (witness.rename names).Refutes (left.rename names.toEmbedding) (right.rename names.toEmbedding) ↔
      witness.Refutes left right := by
  have member : renameStore names witness.initial ∈ (left.rename names.toEmbedding).jointStores
      (right.rename names.toEmbedding) ↔ witness.initial ∈ left.jointStores right := by
    rw [jointStores_rename left right names, List.mem_map]
    refine ⟨?_, fun present => ⟨witness.initial, present, rfl⟩⟩
    rintro ⟨initial, present, same⟩
    have equal : initial = witness.initial := funext fun x => by
      simpa [renameStore] using congrFun same (names x)
    exact equal ▸ present
  unfold CaptureTraceWitness.Refutes CaptureTraceWitness.rename
  dsimp only
  rw [member]
  apply and_congr_right
  intro _
  erw [observe_rename left names _, observe_rename right names _]
  rfl

theorem sentence_rename (names : V ≃ W) (initial : V → Value Atom) :
    (left.rename names.toEmbedding).refinementSentenceAt (right.rename names.toEmbedding)
      (renameStore names initial) = left.refinementSentenceAt right initial := by
  unfold StructuralEntry.refinementSentenceAt
  erw [observe_rename left names initial, observe_rename right names initial]
  rfl

variable [DecidableEq F]

theorem store_verdict_rename (names : V ≃ W) (initial : V → Value Atom) :
    (left.rename names.toEmbedding).refinementFromStore? (right.rename names.toEmbedding)
      (renameStore names initial) = left.refinementFromStore? right initial := by
  have agrees (x : V) : renameStore names initial (names x) = initial x :=
    congrArg initial (names.symm_apply_apply x)
  unfold StructuralEntry.refinementFromStore? StructuralEntry.seed?
  rw [(seeds_rename left names.toEmbedding).2.2 _ _ agrees,
    (seeds_rename right names.toEmbedding).2.2 _ _ agrees]
  rfl

theorem domain_verdict_rename (names : V ≃ W) :
    (left.rename names.toEmbedding).refinementOverCaptures (right.rename names.toEmbedding) =
      left.refinementOverCaptures right := by
  simp only [StructuralEntry.refinementOverCaptures, jointStores_rename, List.map_map, List.isEmpty_map,
    Function.comp_def, store_verdict_rename]

theorem explain_rename (names : V ≃ W) :
    (left.rename names.toEmbedding).explainRefinementOverCaptures? (right.rename names.toEmbedding) =
      (left.explainRefinementOverCaptures? right).map (fun w => w.rename names) := by
  have traces (initial : V → Value Atom) :
      (left.rename names.toEmbedding).explainRefinementFromStore? (right.rename names.toEmbedding)
        (renameStore names initial) = left.explainRefinementFromStore? right initial := by
    have agrees (x : V) : renameStore names initial (names x) = initial x :=
      congrArg initial (names.symm_apply_apply x)
    unfold StructuralEntry.explainRefinementFromStore? StructuralEntry.seed?
    rw [(seeds_rename left names.toEmbedding).2.2 _ _ agrees,
      (seeds_rename right names.toEmbedding).2.2 _ _ agrees]
    rfl
  unfold StructuralEntry.explainRefinementOverCaptures?
  rw [jointStores_rename left right names, List.find?_map]
  simp only [Function.comp_def, store_verdict_rename, Option.bind_map, traces, Option.map_bind, Option.map_map]
  rfl

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.RegisterRename
