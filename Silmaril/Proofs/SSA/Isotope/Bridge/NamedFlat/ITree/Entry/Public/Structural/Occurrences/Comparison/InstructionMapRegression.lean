module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.InstructionMap.Compilation.Thms
import Silmaril.Semantics.ITree.Signature.Execution.Thms
meta import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Defs
meta import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.InstructionMap.Compilation.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open CategoryTheory Silmaril.Logic.ITree
open Silmaril.Elgot.ITree (Request TraceSignature)
open Silmaril.SSA.LambdaRTL (CFG upd)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

private abbrev Name := ULift.{1} Nat
private abbrev bit : PacketType := .coprod .unit .unit
private def sig : PrimitiveSignature Bool := ⟨fun _ => bit, fun _ => bit⟩

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
  cases checked : PacketType.decode bit raw with
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
    [(⟨1⟩, ⟨⟨2⟩, .let1 ⟨3⟩ (.app op (.var ⟨2⟩)) (.term (.br ⟨1⟩ (.var ⟨3⟩)))⟩)]⟩

private def build (op : Bool) :=
  constructStructural sig (graph op) exits fields bit (fun _ => bit) outputs

private def entry (op : Bool) := (build op).get (by cases op <;> decide)

private def forward := ((entry false).checkOccurrenceComparison? (entry true)).get (by decide)
private def rename : sig.Renaming sig := ⟨Bool.not, fun _ => rfl, fun _ => rfl⟩

private def left := (entry false).mapOpcode rename
private def right := (entry true).mapOpcode rename

private def rechecked := (left.checkOccurrenceComparison? right).get
  (((entry false).checkOccurrenceComparison?_isSome_mapOpcode (entry true) rename).trans (by decide))

private def initial : Name → Value Atom := upd (fun _ => .unit) capture (.inr .unit)
private def packet : Denote bit := .inr ⟨⟩

private theorem seed (op : Bool) : (entry op).seed? initial = some packet := by
  cases op <;> decide

-- Rechecking recovers the actual renamed opcode and its typed reply feeds the backedge.
example : (rechecked.leftAdmission.code.block ⟨0, by decide⟩).erase =
    .let₁ (.op true (.var 0)) (.br 0 (.var 0)) := by
  rfl

-- Taking the reply changes the next argument of that same renamed request.
#guard
  let program := left.program
  match program.step (program.start 0 packet) with
  | .inl (.request first next) =>
    match program.step (next (.inl ⟨⟩)) with
    | .inl (.request second _) =>
      match (show Denote bit from first.2), (show Denote bit from second.2) with
      | .inr _, .inl _ => first.1 && second.1
      | _, _ => false
    | _ => false
  | _ => false

example (policy : Model.{0, 0} sig.traceSignature.toSignature) :
    TraceInstitution.Sat policy (rechecked.sentence packet packet) ↔
      TraceInstitution.Sat (policy.reduct renameEvents.hom) (forward.sentence packet packet) :=
  forward.sat_mapOpcode_iff rename rechecked renameEvents primitives packet packet policy

example (policy : Model.{0, 0} sig.traceSignature.toSignature) :
    TraceInstitution.Sat policy (left.refinementSentenceAt right initial) ↔
      TraceInstitution.Sat (policy.reduct renameEvents.hom)
        ((entry false).refinementSentenceAt (entry true) initial) := by
  rw [← rechecked.sentence_eq_original initial packet packet
      (((entry false).seed?_mapOpcode rename initial).trans (seed false))
      (((entry true).seed?_mapOpcode rename initial).trans (seed true)),
    ← forward.sentence_eq_original initial packet packet (seed false) (seed true)]
  exact forward.sat_mapOpcode_iff rename rechecked renameEvents primitives packet packet policy

#guard forward.fromStore? initial == some false && rechecked.fromStore? initial == some false

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
