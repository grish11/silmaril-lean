module

import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Thms

section

namespace Silmaril.Isotope.LetCase.HandledTrace.Regression

open CategoryTheory Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

private inductive Event : Type → Type where
  | ask : Event Unit

private abbrev D := Ty.denote (fun _ : Empty => PUnit.{2})
private abbrev tagged : Ty Empty := .coprod .unit .unit
private abbrev Packet := PUnit.{2} ⊕ PUnit.{2}

local instance : HasTy Bool (Ty Empty) := ⟨fun _ => tagged, fun _ => tagged⟩

private def instructions : InstructionModel D Bool (Tree Event) :=
  ⟨fun replies value => vis .ask (fun _ => if replies then pure value else diverge)⟩

private def policy : Handler Bool Event :=
  fun _ current _ next => current = true ∧ next = true

private def packet : Interface instructions policy := ⟨tagged⟩

private def send (replies : Bool) : Program Bool tagged tagged :=
  ⟨.op replies (.bv 0), .op .bv⟩

private def arrow (replies : Bool) : packet ⟶ packet :=
  Arrow.ofProgram (send replies)

set_option backward.isDefEq.respectTransparency false in
private theorem run_send (replies : Bool) (a : Packet) :
    (send replies).run instructions a =
      vis .ask (fun _ => if replies then pure a else diverge) := by
  change ((pure a : Tree Event Packet) >>= fun b =>
    vis Event.ask (fun _ => if replies then pure b else diverge)) = _
  rw [pure_bind]

private theorem pending_le_complete : arrow false ≤ arrow true := by
  apply Arrow.ofProgram_le_ofProgram.mpr
  intro a x
  erw [run_send, run_send]
  have incl : TraceLE (vis Event.ask (fun _ => diverge)) (vis Event.ask (fun _ => pure a)) :=
    TraceLE.vis Event.ask (fun _ => traceLE_diverge _)
  exact fun p seen => ⟨incl p seen.1, seen.2⟩

private theorem completed_twice (a : Packet) :
    ((send true).seq (send true)).run instructions a =
      vis .ask (fun _ => vis .ask (fun _ => ret a)) := by
  erw [Program.run_seq, run_send]
  change (vis Event.ask (fun _ => (pure a : Tree Event Packet)) >>= _) = _
  erw [vis_bind]
  apply congrArg (vis Event.ask)
  funext reply
  erw [pure_bind, run_send]
  rfl

private theorem pending_twice (a : Packet) :
    ((send false).seq (send false)).run instructions a = vis .ask (fun _ => diverge) := by
  erw [Program.run_seq, run_send]
  change (vis Event.ask (fun _ => (diverge : Tree Event Packet)) >>= _) = _
  erw [vis_bind]
  exact congrArg (vis Event.ask) (funext fun _ => diverge_bind _)

-- Two simultaneous improvements give a strict comparison under the same
-- policy. Starting at true, the two typed exchanges return the right tag.
example : arrow false ≫ arrow false < arrow true ≫ arrow true := by
  apply lt_of_le_not_ge
  · exact (compOrderHom packet packet packet).monotone
      (a := (arrow false, arrow false)) (b := (arrow true, arrow true))
      ⟨pending_le_complete, pending_le_complete⟩
  · intro reverse
    have refines : Program.Refines instructions policy ((send true).seq (send true))
        ((send false).seq (send false)) := Arrow.ofProgram_le_ofProgram.mp reverse
    let a : Packet := .inr PUnit.unit
    let trace : Trace Event Packet := .exchange .ask () (.exchange .ask () (.result a))
    have admits : Replay policy true trace := ⟨true, ⟨rfl, rfl⟩, true, ⟨rfl, rfl⟩, trivial⟩
    have actual : HasTrace (((send true).seq (send true)).run instructions a) trace := by
      erw [completed_twice]
      exact (hasTrace_vis_exchange_iff _ _ _ _).mpr ((hasTrace_vis_exchange_iff _ _ _ _).mpr (out_ret _))
    have impossible := (refines a true trace ⟨actual, admits⟩).1
    erw [pending_twice] at impossible
    have pending := (hasTrace_vis_exchange_iff _ _ _ _).mp impossible
    cases (hasTrace_diverge_iff _).mp pending

-- Quotient identity removes a written let even when the body performs a request.
example : Arrow.ofProgram (A := packet) (B := packet)
    ((Program.id tagged).seq (send true)) = arrow true :=
  Category.id_comp (arrow true)

-- The associative law applies to actual native nested lets.
example : Arrow.ofProgram (A := packet) (B := packet)
    (((send true).seq (send false)).seq (send true)) =
    Arrow.ofProgram (A := packet) (B := packet)
      ((send true).seq ((send false).seq (send true))) :=
  Category.assoc (arrow true) (arrow false) (arrow true)

end Silmaril.Isotope.LetCase.HandledTrace.Regression

end
