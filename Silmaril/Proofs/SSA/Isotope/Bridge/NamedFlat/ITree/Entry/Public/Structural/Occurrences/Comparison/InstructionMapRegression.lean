module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Institution.Refinement.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Institution.Policy.Thms
import Silmaril.Semantics.ITree.Signature.Execution.Thms
meta import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Defs
meta import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Institution.Refinement.Thms
meta import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Institution.Thms
meta import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.InstructionMap.Compilation.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open CategoryTheory Silmaril.Logic.ITree
open OccurrenceInstitution
open Silmaril.Elgot.ITree (Request TraceSignature)
open Silmaril.SSA.LambdaRTL (CFG upd)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

private abbrev Name := ULift.{1} Nat
private abbrev bit : PacketType := .coprod .unit .unit
private def sig : PrimitiveSignature (Fin 3) := ⟨fun _ => bit, fun _ => bit⟩
private abbrev signature : OpcodeSignature := ⟨Fin 3, sig⟩

private def renameRequest (e : Fin 3 ≃ Fin 3) :
    Request sig.traceSignature.toSignature.Event → Request sig.traceSignature.toSignature.Event
  | ⟨_, .ask ⟨op, arg⟩⟩ => ⟨_, .ask ⟨e op, arg⟩⟩

private def renameEvents (e : Fin 3 ≃ Fin 3) : sig.traceSignature ⟶ sig.traceSignature where
  hom :=
    { request := renameRequest e
      reply := fun
        | ⟨_, .ask _⟩, reply => reply }
  request_injective := Function.LeftInverse.injective (g := renameRequest e.symm) <| by
    rintro ⟨_, event⟩
    cases event with
    | ask key =>
      rcases key with ⟨op, arg⟩
      change (⟨_, Elgot.ITree.Finite.Event.ask (⟨e.symm (e op), arg⟩ : sig.Request)⟩ :
        Request sig.traceSignature.toSignature.Event) = ⟨_, .ask ⟨op, arg⟩⟩
      rw [Equiv.symm_apply_apply]
  reply_bijective := by
    rintro ⟨_, event⟩
    cases event
    exact Function.bijective_id

private theorem primitives (e : Fin 3 ≃ Fin 3) (op : Fin 3) (raw : Value Atom) :
    sig.primitive (e op) raw = (renameEvents e).hom.tree id (sig.primitive op raw) := by
  cases checked : PacketType.decode bit raw with
  | none =>
    simp only [PrimitiveSignature.primitive, sig, checked]
    exact (renameEvents e).hom.tree_diverge.symm
  | some arg =>
    simp only [PrimitiveSignature.primitive, sig, checked]
    erw [(renameEvents e).hom.tree_vis]
    let ev : sig.traceSignature.toSignature.Event (Denote bit) :=
      Elgot.ITree.Finite.Event.ask (⟨e op, arg⟩ : sig.Request)
    exact congrArg (Elgot.ITree.vis ev) (funext fun reply =>
      ((renameEvents e).hom.tree_pure (PacketType.encode bit reply)).symm)

private def arrow (e : Fin 3 ≃ Fin 3) : signature ⟶ signature :=
  ⟨⟨e, fun _ => rfl, fun _ => rfl⟩, renameEvents e, fun op raw => primitives e op raw⟩

private def first : signature ⟶ signature := arrow (Equiv.swap 0 1)
private def second : signature ⟶ signature := arrow (Equiv.swap 1 2)

private def capture : Name := ⟨0⟩
private def exits : List Name := []
private def fields (_ : Name) : List Name := []
private def outputs : Fin exits.length → PacketType := Fin.elim0

-- The request reply replaces the packet and the actual successor is the
-- same private block. Both opcodes have the same typed reply family.
private def graph (op : Fin 3) : CFG Name Name (Fin 3) :=
  ⟨.term (.br ⟨1⟩ (.var capture)),
    [(⟨1⟩, ⟨⟨2⟩, .let1 ⟨3⟩ (.app op (.var ⟨2⟩)) (.term (.br ⟨1⟩ (.var ⟨3⟩)))⟩)]⟩

private def build (op : Fin 3) :=
  constructStructural sig (graph op) exits fields bit (fun _ => bit) outputs

private def entry (op : Fin 3) := (build op).get (by
  have which : op = 0 ∨ op = 1 ∨ op = 2 := by
    simp only [Fin.ext_iff]
    omega
  rcases which with rfl | rfl | rfl <;> decide)

private def initial : Name → Value Atom := upd (fun _ => .unit) capture (.inr .unit)
private def packet : Denote bit := .inr ⟨⟩
private def point : Endpoints Name Name signature := ⟨graph 0, graph 2, initial⟩

private def admitted : Admission point exits fields :=
  ⟨bit, bit, outputs, entry 0, entry 2, by decide, packet, packet, by decide, by decide⟩

private def source : Sentence signature exits fields := ⟨point, ⟨admitted⟩⟩
private def direct := admitted.map (first ≫ second)
private def staged := (admitted.map first).map second

example : source.map (𝟙 signature) = source := source.map_id

example : (source.map first).map second = source.map (first ≫ second) :=
  (source.map_comp first second).symm

example : direct.observe = staged.observe :=
  ((source.map (first ≫ second)).compile_eq_admitted direct).symm.trans <|
    (congrArg Sentence.compile (source.map_comp first second)).trans
      (((source.map first).map second).compile_eq_admitted staged)

-- Both checked code paths map the original positions across both opcodes.
example : direct.comparison.leftAdmission.code.erase = staged.comparison.leftAdmission.code.erase := by
  have directCode := admitted.comparison.leftAdmission.erase_mapOpcode
    (first ≫ second).rename direct.comparison.leftAdmission
  have firstCode := admitted.comparison.leftAdmission.erase_mapOpcode
    first.rename (admitted.map first).comparison.leftAdmission
  have secondCode := (admitted.map first).comparison.leftAdmission.erase_mapOpcode
    second.rename staged.comparison.leftAdmission
  exact directCode.trans <| (LambdaSSA.Region.mapInstr_comp first.rename.opcode second.rename.opcode _).symm.trans
    (secondCode.trans (congrArg (LambdaSSA.Region.mapInstr second.rename.opcode) firstCode)).symm

-- The actual final opcode is 2. Its typed reply becomes the next argument.
example : (direct.comparison.leftAdmission.code.block ⟨0, by decide⟩).erase =
    .let₁ (.op 2 (.var 0)) (.br 0 (.var 0)) := by
  rfl

#guard
  let program := direct.left.program
  match program.step (program.start 0 packet) with
  | .inl (.request before next) =>
    match program.step (next (.inl ⟨⟩)) with
    | .inl (.request after _) =>
      match (show Denote bit from before.2), (show Denote bit from after.2) with
      | .inr _, .inl _ => before.1 == 2 && after.1 == 2
      | _, _ => false
    | _ => false
  | _ => false

example (policy : Model.{0, 0} sig.traceSignature.toSignature) :
    policy.reduct (first ≫ second).events.hom =
      (policy.reduct second.events.hom).reduct first.events.hom :=
  Model.reduct_comp first.events.hom second.events.hom policy

example (policy : Model.{0, 0} sig.traceSignature.toSignature) :
    TraceInstitution.Sat policy direct.observe ↔
      TraceInstitution.Sat ((policy.reduct second.events.hom).reduct first.events.hom)
        (point.observe exits fields) := by
  erw [direct.observe_original, ← Model.reduct_comp first.events.hom second.events.hom policy]
  exact source.sat_map_iff (first ≫ second) policy

example (policy : Model.{0, 0} sig.traceSignature.toSignature) :
    TraceInstitution.Sat policy source.compile ↔ TraceInstitution.Sat policy (point.observe exits fields) :=
  (comorphism exits fields).satisfaction signature ⟨policy⟩ ⟨source⟩

#guard direct.comparison.fromStore? initial == some false &&
  staged.comparison.fromStore? initial == some false


-- This silent self-loop has only the finite prefix observation. The
-- productive loop offers a visible request before taking its backedge.
private def quiet : CFG Name Name (Fin 3) :=
  ⟨.term (.br ⟨1⟩ (.var capture)), [(⟨1⟩, ⟨⟨2⟩, .term (.br ⟨1⟩ (.var ⟨2⟩))⟩)]⟩

private def quietEntry := (constructStructural sig quiet exits fields bit (fun _ => bit) outputs).get (by decide)
private def strictPoint : Endpoints Name Name signature := ⟨quiet, graph 0, initial⟩
private def strict : Admission strictPoint exits fields :=
  ⟨bit, bit, outputs, quietEntry, entry 0, by decide, packet, packet, by decide, by decide⟩

private def strictDirect := strict.map (first ≫ second)
private def strictStaged := (strict.map first).map second

#guard strictDirect.comparison.fromStore? initial == some true &&
  strictDirect.swap.comparison.fromStore? initial == some false &&
  strictStaged.comparison.fromStore? initial == some true &&
  strictStaged.swap.comparison.fromStore? initial == some false

example : strict.toSentence.swap.map (first ≫ second) = (strict.toSentence.map (first ≫ second)).swap :=
  strict.toSentence.swap_map (first ≫ second)

private theorem strictAccepts : strict.comparison.fromStore? initial = some true := by
  change some (quietEntry.program.refinementBetween? (entry 0).program 0 packet 0 packet) = some true
  cbv

private theorem strictRejects : strict.swap.comparison.fromStore? initial = some false := by
  change some ((entry 0).program.refinementBetween? quietEntry.program 0 packet 0 packet) = some false
  cbv

example :
    TraceInstitution.Sat (TraceInstitution.allRepliesModel sig.traceSignature)
      ((strict.toSentence.map (first ≫ second)).compile) ∧
    ¬ TraceInstitution.Sat (TraceInstitution.allRepliesModel sig.traceSignature)
      ((strict.swap.toSentence.map (first ≫ second)).compile) := by
  refine ⟨(strict.refinement_iff_valid_map (first ≫ second)).mp strictAccepts _, ?_⟩
  intro passed
  have valid := (TraceInstitution.valid_iff_sat_allReplies _).mpr passed
  have accepted := (strict.swap.refinement_iff_valid_map (first ≫ second)).mpr valid
  exact Bool.noConfusion (Option.some.inj (strictRejects.symm.trans accepted))

example (policy : Model.{0, 0} sig.traceSignature.toSignature) :
    TraceInstitution.Sat policy strictStaged.observe ↔
      TraceInstitution.Sat ((policy.reduct second.events.hom).reduct first.events.hom)
        (strictPoint.observe exits fields) := by
  have source := strict.toSentence.sat_map_iff (first ≫ second) policy
  erw [strictStaged.observe_original, ← Model.reduct_comp first.events.hom second.events.hom policy]
  exact (congrArg (fun φ : Sentence signature exits fields =>
    TraceInstitution.Sat policy (φ.val.observe exits fields)) (strict.toSentence.map_comp first second)) ▸ source


-- Both runners start with opcode 0. A reply exposes opcode 1 only on
-- the right, even when later replies to opcode 1 are denied.
private def delayed : CFG Name Name (Fin 3) :=
  { graph 0 with blocks :=
    [(⟨1⟩, ⟨⟨2⟩, .let1 ⟨3⟩ (.app 0 (.var ⟨2⟩)) (.term (.br ⟨4⟩ (.var ⟨3⟩)))⟩),
     (⟨4⟩, ⟨⟨2⟩, .let1 ⟨3⟩ (.app 1 (.var ⟨2⟩)) (.term (.br ⟨4⟩ (.var ⟨3⟩)))⟩)] }

private def delayedEntry := (constructStructural sig delayed exits fields bit (fun _ => bit) outputs).get (by decide)
private def policyPoint : Endpoints Name Name signature := ⟨graph 0, delayed, initial⟩
private def policyAdmission : Admission policyPoint exits fields :=
  ⟨bit, bit, outputs, entry 0, delayedEntry, by decide, packet, packet, by decide, by decide⟩

private def allInitial : Unit → Prop := fun _ => True
private def deny (_ : sig.Request) : Bool := false
private def allowAt (op : Fin 3) (key : sig.Request) : Bool := decide (key.1 = op)
private def restriction : TraceInstitution.Policy sig.traceSignature.toSignature Unit :=
  Elgot.ITree.Finite.replyHandler (fun key _ => deny key)
private def permission (op : Fin 3) : TraceInstitution.Policy sig.traceSignature.toSignature Unit :=
  Elgot.ITree.Finite.replyHandler (fun key _ => allowAt op key)

private theorem strictPolicy : restriction < permission 0 := by
  apply lt_of_le_not_ge
  · intro ⟨_, ev⟩ _ _ _ impossible
    cases ev
    cases impossible
  · intro wrong
    have allowed : permission 0 ⟨_, .ask ⟨0, packet⟩⟩ () packet () := rfl
    have impossible := wrong ⟨_, .ask ⟨0, packet⟩⟩ () packet () allowed
    cases impossible

private def ambient : LambdaSSA.Semantics.Env Atom := fun _ => .unit

private theorem policyCheck (admits : ∀ key, sig.Reply key → Bool) :
    policyAdmission.left.program.refinementAtUnder? admits policyAdmission.right.program 0 packet = true ↔
      TraceInstitution.Sat (sig.traceModelUnder admits) (policyPoint.observe exits fields) := by
  let a := policyAdmission
  have checked := a.left.program.refinementAtUnder?_iff_traceSat admits packet a.left.entry a.right.entry
    ambient ambient (packetRecord packet) (packetRecord packet)
    (recordAgrees_packetRecord a.left.entry a.left.publicCaptures packet)
    (recordAgrees_packetRecord a.right.entry a.right.publicCaptures packet)
  change _ ↔ TraceInstitution.Sat (sig.traceModelUnder admits)
    (a.left.entry.refinementSentence a.right.entry .leftToRight ambient ambient
      (packetRecord packet) (packetRecord packet)) at checked
  have align : a.left.entry.refinementSentence a.right.entry .leftToRight ambient ambient
      (packetRecord packet) (packetRecord packet) = policyPoint.observe exits fields := by
    let identity := 𝟙 sig.traceSignature
    have packed := a.left.entry.refinementSentence_reindexed a.right.entry identity .leftToRight
      ambient ambient (packetRecord packet) (packetRecord packet)
    have original := a.left.refinementSentence_reindexed a.right identity ambient initial packet packet
      ((decodeSeed?_eq_some_iff _ _ _).mp a.leftSeed) ((decodeSeed?_eq_some_iff _ _ _).mp a.rightSeed)
    exact (TraceInstitution.Sentence.translate_id _).symm.trans
      (packed.trans (original.symm.trans (TraceInstitution.Sentence.translate_id _)))
  exact checked.trans (iff_of_eq (congrArg (TraceInstitution.Sat (sig.traceModelUnder admits)) align))

private theorem satisfiesRestriction :
    TraceInstitution.Sat (restriction.toModel allInitial) (policyPoint.observe exits fields) :=
  (policyCheck (fun key _ => deny key)).mp (by cbv)

private theorem failsPermission :
    ¬ TraceInstitution.Sat ((permission 0).toModel allInitial) (policyPoint.observe exits fields) := by
  intro satisfied
  have accepted := (policyCheck (fun key _ => allowAt 0 key)).mpr satisfied
  have rejected : policyAdmission.left.program.refinementAtUnder? (fun key _ => allowAt 0 key)
      policyAdmission.right.program 0 packet = false := by cbv
  exact Bool.noConfusion (rejected.symm.trans accepted)

example : restriction < permission 0 ∧
    TraceInstitution.Sat (restriction.toModel allInitial) (policyPoint.observe exits fields) ∧
    ¬ TraceInstitution.Sat ((permission 0).toModel allInitial) (policyPoint.observe exits fields) :=
  ⟨strictPolicy, satisfiesRestriction, failsPermission⟩

example : (permission 2).reduct (first ≫ second).events.hom =
    ((permission 2).reduct second.events.hom).reduct first.events.hom :=
  TraceInstitution.Policy.reduct_comp first.events.hom second.events.hom _

example : restriction.reduct (first ≫ second).events.hom <
    ((permission 2).reduct second.events.hom).reduct first.events.hom := by
  erw [← TraceInstitution.Policy.reduct_comp first.events.hom second.events.hom]
  apply lt_of_le_not_ge
  · apply TraceInstitution.Policy.reduct_mono
    intro ⟨_, ev⟩ _ _ _ impossible
    cases ev
    cases impossible
  · intro wrong
    let key : Request sig.traceSignature.toSignature.Event := ⟨_, .ask ⟨0, packet⟩⟩
    have allowed : (permission 2).reduct (first ≫ second).events.hom key () packet () := ⟨packet, rfl, rfl⟩
    obtain ⟨_, _, impossible⟩ := wrong key () packet () allowed
    cases impossible

example : TraceInstitution.Sat (restriction.toModel allInitial) policyAdmission.toSentence.compile ↔
    TraceInstitution.Sat (restriction.toModel allInitial) (policyPoint.observe exits fields) :=
  (policyComorphism exits fields Unit allInitial).satisfaction signature restriction ⟨policyAdmission.toSentence⟩

private def policyArrow := CategoryTheory.homOfLE (x := restriction) (y := permission 0) strictPolicy.le

example : ((policyComorphism exits fields Unit allInitial).ρ.app signature).mod.map policyArrow = policyArrow :=
  rfl

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
