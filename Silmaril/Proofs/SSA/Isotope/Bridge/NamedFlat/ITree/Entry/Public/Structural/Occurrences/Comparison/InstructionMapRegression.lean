module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.InstructionMap.Thms
import Silmaril.Semantics.ITree.Signature.Execution.Thms
meta import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open CategoryTheory Silmaril.Logic.ITree
open Silmaril.Elgot.ITree (Request TraceSignature)
open Silmaril.SSA.LambdaRTL (CFG upd)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

private abbrev Name := ULift.{1} Nat
private abbrev bit : PacketType := .coprod .unit .unit
private def sig : PrimitiveSignature Bool := ⟨fun _ => .unit, fun _ => bit⟩

private def renameRequest : Request sig.traceSignature.toSignature.Event → Request sig.traceSignature.toSignature.Event
  | ⟨_, .ask ⟨op, arg⟩⟩ => ⟨_, .ask ⟨!op, arg⟩⟩

private def renameEvents : sig.traceSignature ⟶ sig.traceSignature where
  hom :=
    { request := renameRequest
      reply := fun
        | ⟨_, .ask _⟩, reply => reply }
  request_injective := Function.LeftInverse.injective (g := renameRequest) <| by
    rintro ⟨_, event⟩
    cases event with
    | ask key => rcases key with ⟨op, arg⟩; cases op <;> rfl
  reply_bijective := by
    rintro ⟨_, event⟩
    cases event
    exact Function.bijective_id

private theorem primitives (op : Bool) (raw : Value Atom) :
    sig.primitive (!op) raw = renameEvents.hom.tree id (sig.primitive op raw) := by
  cases checked : PacketType.decode .unit raw with
  | none =>
    simp only [PrimitiveSignature.primitive, sig, checked]
    exact renameEvents.hom.tree_diverge.symm
  | some arg =>
    simp only [PrimitiveSignature.primitive, sig, checked]
    erw [renameEvents.hom.tree_vis]
    let ev : sig.traceSignature.toSignature.Event (Denote bit) :=
      Elgot.ITree.Finite.Event.ask (⟨!op, arg⟩ : sig.Request)
    exact congrArg (Elgot.ITree.vis ev) (funext fun reply =>
      (renameEvents.hom.tree_pure (PacketType.encode bit reply)).symm)

private def capture : Name := ⟨0⟩
private def exits : List Name := []
private def fields (_ : Name) : List Name := []
private def outputs : Fin exits.length → PacketType := Fin.elim0

-- The request reply replaces the packet and the actual successor is the
-- same private block. Both opcodes have the same typed reply family.
private def graph (op : Bool) : CFG Name Name Bool :=
  ⟨.term (.br ⟨1⟩ (.var capture)),
    [(⟨1⟩, ⟨⟨2⟩, .let1 ⟨3⟩ (.app op .unit) (.term (.br ⟨1⟩ (.var ⟨3⟩)))⟩)]⟩

private def build (op : Bool) :=
  constructStructural sig (graph op) exits fields bit (fun _ => bit) outputs

private def entry (op : Bool) := (build op).get (by cases op <;> decide)

private def forward := ((entry false).checkOccurrenceComparison? (entry true)).get (by decide)
private def backward := ((entry true).checkOccurrenceComparison? (entry false)).get (by decide)

private def initial : Name → Value Atom := upd (fun _ => .unit) capture (.inr .unit)
private def packet : Denote bit := .inr ⟨⟩

private theorem seed (op : Bool) : (entry op).seed? initial = some packet := by
  cases op <;> decide

private theorem leftCode :
    backward.leftAdmission.code.erase = forward.leftAdmission.code.erase.mapInstr Bool.not := by
  change LambdaSSA.Region.cfg (.br 0 (.var 0)) 1 _ = LambdaSSA.Region.cfg (.br 0 (.var 0)) 1 _
  congr 1
  funext i
  have hi : i = ⟨0, by decide⟩ := Fin.eq_zero i
  subst i
  rfl

private theorem rightCode :
    backward.rightAdmission.code.erase = forward.rightAdmission.code.erase.mapInstr Bool.not := by
  change LambdaSSA.Region.cfg (.br 0 (.var 0)) 1 _ = LambdaSSA.Region.cfg (.br 0 (.var 0)) 1 _
  congr 1
  funext i
  have hi : i = ⟨0, by decide⟩ := Fin.eq_zero i
  subst i
  rfl

private theorem slots : (entry true).occurrenceStore packet = (entry false).occurrenceStore packet := by
  rfl

-- The recertified true opcode is immediately followed by a backedge.
example : (backward.leftAdmission.code.block ⟨0, by decide⟩).erase =
    .let₁ (.op true .unit) (.br 0 (.var 0)) := by
  rfl

example (policy : Model.{0, 0} sig.traceSignature.toSignature) :
    TraceInstitution.Sat policy (backward.sentence packet packet) ↔
      TraceInstitution.Sat (policy.reduct renameEvents.hom) (forward.sentence packet packet) :=
  forward.sat_mapInstr_iff (opcode := Bool.not) backward renameEvents primitives packet packet
    leftCode rightCode slots slots.symm policy

example (policy : Model.{0, 0} sig.traceSignature.toSignature) :
    TraceInstitution.Sat policy ((entry true).refinementSentenceAt (entry false) initial) ↔
      TraceInstitution.Sat (policy.reduct renameEvents.hom)
        ((entry false).refinementSentenceAt (entry true) initial) := by
  rw [← backward.sentence_eq_original initial packet packet (seed true) (seed false),
    ← forward.sentence_eq_original initial packet packet (seed false) (seed true)]
  exact forward.sat_mapInstr_iff (opcode := Bool.not) backward renameEvents primitives packet packet
    leftCode rightCode slots slots.symm policy

#guard forward.fromStore? initial == some false && backward.fromStore? initial == some false

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
