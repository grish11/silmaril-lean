module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.InternalExamples

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (BlockInput Primitive Transfer region splitTransfer)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (Atom Denote PacketType PrimitiveSignature Program)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree
  (Tree Trace HasTrace ret vis diverge iterate_fixpoint iterate_forever vis_bind hasTrace_vis_exchange_iff out_ret)
open Silmaril.Elgot.ITree.Finite (Event evaluate transition)

private def bit : PacketType := .coprod .unit .unit
private def replyType : PacketType := .coprod bit .unit
private def sig : PrimitiveSignature Unit := ⟨fun _ => bit, fun _ => replyType⟩
private abbrev Events := Event sig.Request sig.Reply

private def packets (i : Fin 2) : PacketType := if i.val = 0 then bit else replyType
private def exits (_ : Fin 2) : PacketType := .unit

-- The selected row forwards its reply to the old case row. A continue
-- reply supplies the next poll's argument; a stop reply takes exit one.
private def polling : FiniteCFG Unit 2 2 1 where
  entry := .br 0 (.bv 0)
  block i :=
    if i.val = 0 then .let₁ (.op () (.bv 0)) (.br 1 (.bv 0))
    else .case (.bv 0) (.br 0 (.bv 0)) (.br 3 (.bv 0))

private def checked : Checked sig (.snoc .nil bit) packets exits polling :=
  (check sig (.snoc .nil bit) packets exits polling).get (by decide)

private def built :=
  (construct sig (fun i => (checked.shape.table i).1) exits checked.emitted.code).get (by decide)

private def dispatcher := built.program

example : (checked.emitted.code.block 2).erase = .let₂ (.var 0) (.br 1 (.var 0)) := rfl

private def key (input : Denote bit) : sig.Request := ⟨(), input⟩

private def fresh (input : Denote bit) (reply : Denote replyType) : dispatcher.State := by
  refine ⟨⟨.inl ⟨2, by decide⟩, ?_⟩⟩
  change Denote bit × Denote replyType
  exact (input, reply)

private def decideReply (reply : Denote replyType) : dispatcher.State := by
  refine ⟨⟨.inl ⟨1, by decide⟩, ?_⟩⟩
  exact reply

private def exitState : dispatcher.State := ⟨⟨.inr 1, ⟨⟩⟩⟩

private theorem poll_step (input : Denote bit) :
    dispatcher.step (dispatcher.start 0 input) = .inl (.request (key input) (fresh input)) := rfl

private theorem fresh_step (input : Denote bit) (reply : Denote replyType) :
    dispatcher.step (fresh input reply) = .inr (decideReply reply) := rfl

private theorem continue_step (input : Denote bit) :
    dispatcher.step (decideReply (.inl input)) = .inr (dispatcher.start 0 input) := rfl

private theorem stop_step : dispatcher.step (decideReply (.inr ⟨⟩)) = .inr exitState := rfl

private theorem ret_eq_pure {A : Type 1} (value : A) : ret (E := Events) value = pure value := rfl

private noncomputable def runState (state : dispatcher.State) : Tree Events (Transfer Atom) :=
  evaluate dispatcher.step state >>= fun r => pure (FiniteCFG.packedTreeOutput (Program.renderResult r))

private theorem run_jump {here next : dispatcher.State} (jump : dispatcher.step here = .inr next) :
    runState here = runState next := by
  unfold runState evaluate
  rw [congrFun (iterate_fixpoint (transition dispatcher.step)) here]
  simp only [transition, jump, ret_eq_pure, pure_bind, Sum.elim_inr]

private theorem run_exit : runState exitState = pure (FiniteCFG.packedTreeOutput (1, .unit)) := by
  unfold runState evaluate
  rw [congrFun (iterate_fixpoint (transition dispatcher.step)) exitState]
  have exitStep : dispatcher.step exitState = .inl (.result ⟨⟨1, ⟨⟩⟩⟩) := rfl
  simp only [transition, exitStep, ret_eq_pure, pure_bind, Sum.elim_inl]
  rfl

private theorem poll_again (input : Denote bit) :
    runState (dispatcher.start 0 input) = vis (Event.ask (key input)) (fun
      | .inl next => runState (dispatcher.start 0 next)
      | .inr _ => pure (FiniteCFG.packedTreeOutput (1, .unit))) := by
  have first : runState (dispatcher.start 0 input) =
      vis (Event.ask (key input)) (fun reply => runState (fresh input reply)) := by
    unfold runState evaluate
    rw [congrFun (iterate_fixpoint (transition dispatcher.step)) (dispatcher.start 0 input)]
    simp only [transition, poll_step, vis_bind, ret_eq_pure, pure_bind, Sum.elim_inr]
  rw [first]
  congr 1
  funext reply
  rw [run_jump (fresh_step input reply)]
  cases reply with
  | inl next => exact run_jump (continue_step next)
  | inr done =>
    cases done
    exact (run_jump stop_step).trans run_exit

private def env (input : Denote bit) : Env Atom := fun _ => bit.encode input
private def firstBit : Denote bit := .inl ⟨⟩
private def nextBit : Denote bit := .inr ⟨⟩

private theorem codec_id (value : Value Atom) : valueCodec id value = value := by
  induction value <;> simp_all only [valueCodec, id_eq]

private theorem modelAgrees : PrimitivesAgree sig.primitive sig.primitive id := by
  intro op value
  rw [codec_id, show valueCodec (id : Atom → Atom) = id from funext codec_id, id_map]

private noncomputable def original (input : Denote bit) : Tree Events (Transfer Atom) :=
  resultCodec id <$> (region sig.primitive (env input) polling.erase >>=
    fun out => pure (FiniteCFG.packedTreeOutput out))

private theorem source_packed (input : Denote bit) :
    original input = built.packed.observe (env input) (env input) :=
  checked.emitted.public_run built (env input) (env input) (env input) id modelAgrees
    (codec_id _).symm

private theorem packed_state (input : Denote bit) :
    built.packed.observe (env input) (env input) = runState (dispatcher.start 0 input) := by
  rw [built.packed.observe_eq input _ _ (fun _ => rfl)]
  change (dispatcher.observe 0 input >>= fun out => pure (FiniteCFG.packedTreeOutput out)) = _
  rw [dispatcher.observe_eq 0 input]
  simp only [runState, bind_assoc, pure_bind]

private def twoPolls : Trace Events (Transfer Atom) :=
  .exchange (.ask (key firstBit)) (.inl nextBit)
    (.exchange (.ask (key nextBit)) (.inr ⟨⟩) (.result (FiniteCFG.packedTreeOutput (1, .unit))))

/-- The first reply changes the second request, and the second reply
terminates at the second ordered exit in both actual runs. -/
theorem polls_twice_then_exits :
    HasTrace (original firstBit) twoPolls ∧
      HasTrace (built.packed.observe (env firstBit) (env firstBit)) twoPolls := by
  have trace : HasTrace (runState (dispatcher.start 0 firstBit)) twoPolls := by
    unfold twoPolls
    rw [poll_again firstBit]
    erw [hasTrace_vis_exchange_iff]
    change HasTrace (runState (dispatcher.start 0 nextBit)) _
    rw [poll_again nextBit]
    erw [hasTrace_vis_exchange_iff]
    exact out_ret _
  rw [source_packed, packed_state]
  exact ⟨trace, trace⟩

-- This terminal jump directly re-enters the selected row. A primitive
-- model that answers silently gives a genuine silent infinite path.
private def self : FiniteCFG Unit 1 1 1 :=
  ⟨.br 0 (.bv 0), fun _ => .let₁ (.op () (.bv 0)) (.br 0 (.bv 1))⟩

private def selfChecked : Checked sig (.snoc .nil bit) (fun _ => bit) (fun _ => .unit) self :=
  (check sig (.snoc .nil bit) (fun _ => bit) (fun _ => .unit) self).get (by decide)

private def selfBuilt :=
  (construct sig (fun i => (selfChecked.shape.table i).1) (fun _ => .unit) selfChecked.emitted.code).get (by decide)

example : selfBuilt.program.locals = 2 := rfl
example : (selfChecked.emitted.code.block 1).erase = .let₂ (.var 0) (.br 0 (.var 1)) := rfl

private def silent : Primitive Events Unit Atom := fun _ arg => pure (.inl arg)

private theorem source_diverges :
    region silent (env firstBit) self.erase = diverge := by
  let step (p : BlockInput Atom 1) : Tree Events (Transfer Atom ⊕ BlockInput Atom 1) :=
    region silent (extend (env firstBit) p.2) (self.block p.1).erase >>= fun out => pure (splitTransfer 1 out)
  have loop : step = fun p => pure (.inr p) := by
    funext p
    rcases p with ⟨label, payload⟩
    have zero : label = 0 := Subsingleton.elim _ _
    subst label
    change (region silent (extend (env firstBit) payload) (.let₁ (.op () (.var 0)) (.br 0 (.var 1))) >>=
      fun out => pure (splitTransfer 1 out)) = _
    simp [region, LambdaSSA.Semantics.Interaction.term, silent, splitTransfer]
  change (region silent (env firstBit) (.br 0 (.var 0)) >>= fun out =>
    Sum.elim pure (iter step) (splitTransfer 1 out)) = _
  rw [loop]
  simp [region, LambdaSSA.Semantics.Interaction.term, splitTransfer, iterate_forever]

theorem self_jump_diverges :
    region silent (env firstBit) self.erase = diverge ∧
      region silent (env firstBit) selfChecked.emitted.code.erase = diverge :=
  ⟨source_diverges, (selfChecked.emitted.preserves_run silent _).symm.trans source_diverges⟩

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.InternalExamples
