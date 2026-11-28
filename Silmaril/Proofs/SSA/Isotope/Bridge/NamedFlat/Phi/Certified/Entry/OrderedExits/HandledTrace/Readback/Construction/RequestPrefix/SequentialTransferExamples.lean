module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Capture.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.SequentialTransferExamples

open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (BlockInput Transfer region splitTransfer)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree Trace HasTrace vis iterate_fixpoint vis_bind hasTrace_vis_exchange_iff out_ret)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom Denote PacketType PrimitiveSignature)
open NamedFlat.Capture.Carry (inferSlots packetTypesList)
open EffectfulEntry.Multiple.Computed.Block.Graph.Capture renaming compile → compileCaptured, Compiled → CaptureCompiled

private abbrev bit : PacketType := .coprod .unit .unit
private abbrev control : PacketType := .coprod bit bit

private abbrev sig : PrimitiveSignature Bool :=
  ⟨fun _ => .product control bit, fun _ => control⟩
private abbrev Events := Event sig.Request sig.Reply

private def inputs : BoundCtx PacketType 2 := .snoc (.snoc .nil bit) control
private def outputs (i : Fin 2) : PacketType := if i.val = 0 then .unit else bit

/-- Two ordinary request binds run per visit. Each reads an immutable
caller slot, and the first reply supplies the second request's control. -/
private def source : FiniteCFG Bool 2 2 2 where
  entry := .br 1 (.bv 0)
  block i := if i.val = 0 then
    .let₁ (.op false (.pair (.bv 0) (.bv 2)))
      (.let₁ (.op true (.pair (.bv 0) (.bv 3))) (.br 1 (.bv 0)))
  else .case (.bv 0) (.br 0 (.bv 1)) (.br 3 (.bv 0))

private def build := compileCaptured sig inputs (fun _ => control) outputs source
private def built : CaptureCompiled sig inputs (fun _ => control) outputs source := build.get (by decide +kernel)

example : (EffectfulEntry.Multiple.Computed.Block.Graph.compile sig inputs
    (fun _ => control) outputs source).isNone = true := rfl

-- Slot zero is used only by the entry and needs no copy in the loop.
example : inferSlots source = [1] := rfl
example (i : Fin 2) : packetTypesList (fun _ : Fin 2 => control) inputs (inferSlots source) i =
    .product control bit := rfl

private def rowMatches (i : Fin (2 + built.checked.shape.count)) (expected : Region Bool) : Bool :=
  let packed := built.checked.publicReadback
  (commonRow (2 + built.checked.shape.count + 2)
    (packed.packed.target.block (i.cast packed.provenance.count)).erase expected).isSome

example : built.checked.shape.count = 5 := by decide +kernel
example : rowMatches 0 (.br 2 (.var 0)) = true := by decide +kernel
example : rowMatches 1 (.let₂ (.var 0) (.case (.var 1)
    (.br 0 (.pair (.var 2) (.var 1))) (.br 8 (.var 0)))) = true := by decide +kernel
example : rowMatches 2 (.let₂ (.var 0) (.br 3 (.pair (.pair (.var 2) (.var 1)) (.var 0)))) = true :=
  by decide +kernel
example : rowMatches 3 (.let₂ (.var 0) (.let₂ (.var 1)
    (.let₁ (.op false (.pair (.var 0) (.var 2))) (.br 4 (.pair (.var 5) (.var 0)))))) = true :=
  by decide +kernel
example : rowMatches 4 (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1)
    (.br 5 (.pair (.pair (.pair (.var 1) (.var 0)) (.var 2)) (.var 4)))))) = true := by decide +kernel
example : rowMatches 5 (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1)
    (.let₁ (.op true (.pair (.var 4) (.var 2))) (.br 6 (.pair (.var 7) (.var 0))))))) = true :=
  by decide +kernel
example : rowMatches 6 (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1)
    (.br 1 (.pair (.var 6) (.var 2))))))) = true := by decide +kernel

private def first : Denote bit := .inl ⟨⟩
private def second : Denote bit := .inr ⟨⟩

private def env : Env Atom := fun i => if i = 0 then control.encode (.inl first) else bit.encode second
private def key (op : Bool) (current : Denote control) : sig.Request := ⟨op, (current, second)⟩

private noncomputable def step (state : BlockInput Atom 2) : Tree Events (Transfer Atom ⊕ BlockInput Atom 2) :=
  blockStep sig.primitive source env state

private theorem request_tree (req : sig.Request) :
    sig.primitive req.1 ((sig.argument req.1).encode req.2) =
      vis (.ask req) (fun reply : sig.Reply req => pure ((sig.reply req.1).encode reply)) := by
  cases req with
  | mk op arg =>
    unfold PrimitiveSignature.primitive
    rw [Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PacketType.decode_encode]

private theorem poll (current : Denote control) :
    iter step (0, control.encode current) =
      vis (.ask (key false current)) fun firstReply : sig.Reply (key false current) =>
        vis (.ask (key true firstReply)) fun secondReply : sig.Reply (key true firstReply) =>
          iter step (1, control.encode secondReply) := by
  rw [congrFun (iterate_fixpoint step) (0, control.encode current)]
  have row : (source.block 0).erase =
      .let₁ (.op false (.pair (.var 0) (.var 2)))
        (.let₁ (.op true (.pair (.var 0) (.var 3))) (.br 1 (.var 0))) := rfl
  simp only [step, blockStep, transfer, row, region, LambdaSSA.Semantics.Interaction.term,
    map_eq_pure_bind, bind_assoc, pure_bind]
  let firstKey := key false current
  change (sig.primitive firstKey.1 ((sig.argument firstKey.1).encode firstKey.2) >>= _) = _
  rw [request_tree firstKey, vis_bind]
  simp only [pure_bind]
  apply congrArg (vis (E := Events) (.ask firstKey))
  funext firstReply
  let nextKey := key true firstReply
  change (sig.primitive nextKey.1 ((sig.argument nextKey.1).encode nextKey.2) >>= _) = _
  rw [request_tree nextKey, vis_bind]
  simp [splitTransfer]
  rfl

private theorem route_row : (source.block 1).erase = .case (.var 0) (.br 0 (.var 1)) (.br 3 (.var 0)) := rfl

private theorem repeat_visit (current : Denote bit) :
    iter step (1, control.encode (.inl current)) = iter step (0, control.encode (.inl current)) := by
  rw [congrFun (iterate_fixpoint step) (1, control.encode (.inl current))]
  simp [step, blockStep, transfer, route_row, region, LambdaSSA.Semantics.Interaction.term, PacketType.encode, splitTransfer]

private theorem return_visit (payload : Denote bit) :
    iter step (1, control.encode (.inr payload)) = pure (1, bit.encode payload) := by
  rw [congrFun (iterate_fixpoint step) (1, control.encode (.inr payload))]
  simp [step, blockStep, transfer, route_row, region, LambdaSSA.Semantics.Interaction.term, PacketType.encode, splitTransfer]

private noncomputable def written : Tree Events (Transfer Atom) :=
  resultCodec id <$> (region sig.primitive env source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out))

private theorem codec_id (val : Value Atom) : valueCodec id val = val := by
  induction val <;> simp_all only [valueCodec, id_eq]

/-- The packed ambient environment is empty. Its input comes from the
original entry and the detected slot of the original ambient evaluator. -/
theorem packed_agrees (result : CaptureCompiled sig inputs (fun _ => control) outputs source) :
    written = result.checked.publicReadback.packed.observe (fun _ => .unit) (result.inputRecord id env) := by
  have primitives : PrimitivesAgree sig.primitive sig.primitive id := by
    intro op val
    rw [codec_id, show valueCodec (id : Atom → Atom) = id from funext codec_id, id_map]
  exact result.public_run env (fun _ => .unit) id primitives

private def twice : Trace Events (Transfer Atom) :=
  .exchange (.ask (key false (.inl first))) (.inl second)
    (.exchange (.ask (key true (.inl second))) (.inl second)
      (.exchange (.ask (key false (.inl second))) (.inl first)
        (.exchange (.ask (key true (.inl first))) (.inr first)
          (.result (FiniteCFG.packedTreeOutput (1, bit.encode first))))))

theorem packed_two_visits :
    HasTrace (built.checked.publicReadback.packed.observe (fun _ => .unit) (built.inputRecord id env)) twice := by
  rw [← packed_agrees built]
  unfold written twice
  have start : region sig.primitive env source.erase = iter step (1, control.encode (.inl first)) := by
    have entry : source.entry.erase = .br 1 (.var 0) := rfl
    simp only [FiniteCFG.erase, region, entry, LambdaSSA.Semantics.Interaction.term, pure_bind]
    have seed : splitTransfer 2 (1, env 0) = .inr (1, control.encode (.inl first)) := rfl
    rw [seed, Sum.elim_inr]
    have steps : (fun p : BlockInput Atom 2 => region sig.primitive (extend env p.2)
        (source.block p.1).erase >>= fun out => pure (splitTransfer 2 out)) = step := by
      funext p
      simp only [step, blockStep, transfer, map_eq_pure_bind]
    exact congrFun (congrArg iter steps) (1, control.encode (.inl first))
  rw [start, repeat_visit first, poll (.inl first)]
  simp only [map_eq_pure_bind, bind_assoc, vis_bind]
  erw [hasTrace_vis_exchange_iff]
  erw [hasTrace_vis_exchange_iff]
  change HasTrace (iter step (1, control.encode (.inl second)) >>= _) _
  rw [repeat_visit second, poll (.inl second), vis_bind]
  erw [hasTrace_vis_exchange_iff]
  rw [vis_bind]
  erw [hasTrace_vis_exchange_iff]
  rw [return_visit first, pure_bind]
  simp only [resultCodec, codec_id, pure_bind]
  exact out_ret _

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.SequentialTransferExamples
