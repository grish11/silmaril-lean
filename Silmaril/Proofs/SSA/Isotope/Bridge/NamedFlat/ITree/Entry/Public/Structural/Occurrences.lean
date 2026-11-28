module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.NamedSSA.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Thms
import Mathlib.Data.List.Forall2

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
open Silmaril.SSA.LambdaRTL (CFG Val upd)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction (region)
open Phi.Certified.Entry.OrderedExits.Readback (packetValue)

variable {V : Type 1} {n : Nat} {seed : Val (Fin n)} {ty : PacketType}
  (typing : StructuralSeed seed ty) (names : Fin n → V)

private theorem assignment_count (packet : Denote ty) :
    (typing.assignment names packet).length = (typing.footprint names).length := by
  induction typing with
  | var | unit => rfl
  | pair left right ihl ihr =>
    rcases packet with ⟨a, b⟩
    simp [StructuralSeed.assignment, StructuralSeed.footprint, ihl a, ihr b]

private theorem assignment_typed (initial : V → Value Atom) (packet : Denote ty)
    (checked : packetValue (StructuralSeed.captureEnv names initial) seed = PacketType.encode ty packet) :
    List.Forall₂ (fun (value : V × Value Atom) (slot : V × PacketType) =>
      value.2 = initial slot.1 ∧ ∃ p : Denote slot.2, value.2 = PacketType.encode slot.2 p)
      (typing.assignment names packet) (typing.footprint names) := by
  induction typing with
  | var slot arg =>
    exact .cons ⟨by simpa [packetValue, StructuralSeed.captureEnv, slot.isLt] using checked.symm,
      ⟨packet, rfl⟩⟩ .nil
  | unit => exact .nil
  | pair left right ihl ihr =>
    rcases packet with ⟨a, b⟩
    have parts := Value.pair.inj checked
    exact List.rel_append (ihl a parts.1) (ihr b parts.2)

private theorem eval_operand {F : Type} (sig : PrimitiveSignature F) (packet : Denote ty) (offset : Nat)
    (slots : Register → Value Atom)
    (reads : ∀ i (h : i < (typing.assignment names packet).length),
      slots ⟨offset + i⟩ = ((typing.assignment names packet)[i]'h).2) :
    (typing.occurrenceOperand names offset).eval (treeModel sig.primitive) slots = PacketType.encode ty packet := by
  induction typing generalizing offset with
  | var slot arg => simpa [StructuralSeed.occurrenceOperand, Val.eval, StructuralSeed.assignment] using
      (reads 0 (by simp [StructuralSeed.assignment]))
  | unit => rfl
  | pair left right ihl ihr =>
    rcases packet with ⟨a, b⟩
    change _ = Value.pair (PacketType.encode _ a) (PacketType.encode _ b)
    simp only [StructuralSeed.occurrenceOperand, Val.eval, treeModel, Value.pair.injEq]
    constructor
    · apply ihl a offset
      intro i hi
      have bound : i < (left.assignment names a ++ right.assignment names b).length := by
        simp only [List.length_append]
        omega
      exact (reads i bound).trans (congrArg Prod.snd (List.getElem_append_left hi))
    · apply ihr b (offset + (left.footprint names).length)
      intro i hi
      rw [← assignment_count left names a, Nat.add_assoc]
      have bound : (left.assignment names a).length + i <
          (left.assignment names a ++ right.assignment names b).length := by
        simpa only [List.length_append, Nat.add_lt_add_iff_left] using hi
      refine (reads ((left.assignment names a).length + i) bound).trans ?_
      change ((left.assignment names a ++ right.assignment names b)[(left.assignment names a).length + i]'bound).2 = _
      simp only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

variable [DecidableEq V] {K : Type 1} [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source : CFG V K F}
  {exits : List K} {fields : K → List V} {outputs : Fin exits.length → PacketType}
  (entry : StructuralEntry signature source exits fields ty outputs)

theorem slots_typed (initial : V → Value Atom) (packet : Denote ty)
    (checked : entry.seed? initial = some packet) (i : Fin entry.footprint.length) :
    entry.occurrenceStore packet (entry.occurrenceNames i) = initial entry.footprint[i.val].1 ∧
      ∃ v : Denote (entry.occurrenceContext.get i),
        entry.occurrenceStore packet (entry.occurrenceNames i) =
          PacketType.encode (entry.occurrenceContext.get i) v := by
  have aligned := assignment_typed entry.typedSeed (fun i => entry.names[i.val]) initial packet
    ((decodeSeed?_eq_some_iff ty _ packet).mp checked)
  change List.Forall₂ (fun (value : V × Value Atom) (slot : V × PacketType) =>
    value.2 = initial slot.1 ∧ ∃ p : Denote slot.2, value.2 = PacketType.encode slot.2 p)
    (entry.assignment packet) entry.footprint at aligned
  have bound : i.val < (entry.assignment packet).length := aligned.length_eq.symm ▸ i.isLt
  have localSlot := aligned.get bound i.isLt
  rw [show entry.occurrenceContext.get i = entry.footprint[i.val].2 from
    congrFun (BoundCtx.get_ofFin (fun j : Fin entry.footprint.length => entry.footprint[j.val].2)) i]
  simpa only [StructuralEntry.occurrenceNames, StructuralEntry.occurrenceStore,
    List.getElem?_eq_getElem bound, Option.elim_some, List.get_eq_getElem] using localSlot

theorem observe_eq_public (packet : Denote ty) :
    entry.observeOccurrences packet =
      (entry.program.observe 0 packet >>= fun out => pure (FiniteCFG.packedTreeOutput out)) := by
  let model := treeModel signature.primitive
  let original := entry.program.compile 0
  let publicStore := Program.store (inputs := fun _ : Fin 1 => ty) 0 packet
  have closed : RoundTrip.PacketClosed original :=
    Reverse.elaborateAt_packetClosed original entry.program.exits entry.entry.captures rfl
      ((elaborateAt_eq original entry.program.exits entry.entry.captures).trans entry.entry.accepted)
  have steps : CFG.Cyclic.stepSSA model original.blocks (entry.occurrenceStore packet) =
      CFG.Cyclic.stepSSA model original.blocks publicStore := by
    funext pending
    obtain ⟨label, payload⟩ := pending
    exact (RoundTrip.step_packetClosed_obs model original.blocks closed _
      (label, payload, fun _ => .unit)).symm.trans
      (RoundTrip.step_packetClosed_obs model original.blocks closed _
        (label, payload, fun _ => .unit))
  have value := eval_operand entry.typedSeed (fun i => entry.names[i.val]) signature packet 0
    (entry.occurrenceStore packet) (fun i bound => by
      change i < (entry.assignment packet).length at bound
      simp only [StructuralEntry.occurrenceStore, Nat.zero_add, List.getElem?_eq_getElem bound, Option.elim_some]
      rfl)
  have enters : entry.occurrenceGraph.entry.evalJump model (entry.occurrenceStore packet) =
      original.entry.evalJump model publicStore := by
    let label : entry.program.Address := ⟨entry.program.entry 0⟩
    change pure (label, entry.occurrenceOperand.eval model (entry.occurrenceStore packet)) =
      pure (label, publicStore ⟨0⟩)
    rw [show entry.occurrenceOperand.eval model (entry.occurrenceStore packet) = _ from value]
    rfl
  have run : CFG.Cyclic.runSSA model entry.occurrenceGraph (entry.occurrenceStore packet) =
      CFG.Cyclic.runSSA model original publicStore := by
    unfold CFG.Cyclic.runSSA
    rw [show entry.occurrenceGraph.blocks = original.blocks from rfl, steps, enters]
  unfold StructuralEntry.observeOccurrences Program.observe
  rw [show CFG.Cyclic.runSSA (treeModel signature.primitive) entry.occurrenceGraph (entry.occurrenceStore packet) = _ from run]
  simp only [bind_assoc, pure_bind]
  rfl

theorem observe_eq_elaborated (admitted : OccurrenceAdmission entry) (packet : Denote ty) :
    entry.observeOccurrences packet =
      (region signature.primitive (fun i => entry.occurrenceStore packet ⟨i⟩) admitted.code.erase >>=
        fun out => pure (FiniteCFG.packedTreeOutput out)) := by
  have observed := run_tree signature.primitive entry.occurrenceGraph entry.program.exits
    entry.occurrenceNames admitted.accepted (entry.occurrenceStore packet)
    (fun i => entry.occurrenceStore packet ⟨i⟩) (fun _ => rfl)
  rw [← observed]
  simp only [StructuralEntry.observeOccurrences, bind_assoc, pure_bind]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences
