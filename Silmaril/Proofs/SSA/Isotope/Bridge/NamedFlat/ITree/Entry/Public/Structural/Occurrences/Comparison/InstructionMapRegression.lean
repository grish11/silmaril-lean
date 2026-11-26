module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Institution.Thms
import Silmaril.Semantics.ITree.Signature.Execution.Thms
meta import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Defs
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

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
