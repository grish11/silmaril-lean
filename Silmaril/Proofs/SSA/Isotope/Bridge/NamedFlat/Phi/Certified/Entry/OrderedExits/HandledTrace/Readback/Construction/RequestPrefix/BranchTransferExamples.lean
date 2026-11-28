module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Capture.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.BranchTransferExamples

open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (BlockInput Transfer region splitTransfer)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree Trace HasTrace vis iterate_fixpoint vis_bind hasTrace_vis_exchange_iff out_ret)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom Denote PacketType PrimitiveSignature)
open NamedFlat.Capture.Carry (inferSlots)
open EffectfulEntry.Multiple.Computed.Block.Graph.Capture renaming compile → compileCaptured, Compiled → CaptureCompiled

private abbrev bit : PacketType := .coprod .unit .unit
private abbrev control : PacketType := .coprod bit bit

private abbrev sig : PrimitiveSignature Bool :=
  ⟨fun _ => .product bit bit, fun op => if op then control else bit⟩
private abbrev Events := Event sig.Request sig.Reply

private def inputs : BoundCtx PacketType 2 := .snoc (.snoc .nil bit) control
private def packets (_ : Fin 1) : PacketType := control
private def outputs (_ : Fin 2) : PacketType := bit

/-- The left arm polls twice and returns to the original row. The right
arm has a silent route to the second exit and a separate request route to
the first. Requests in either arm read the older caller capture. -/
private def source : FiniteCFG Bool 1 2 2 where
  entry := .br 0 (.bv 0)
  block _ := .case (.bv 0)
    (.let₁ (.op false (.pair (.bv 0) (.bv 3)))
      (.let₁ (.op true (.pair (.bv 0) (.bv 4))) (.br 0 (.bv 0))))
    (.case (.bv 0) (.br 2 (.bv 1))
      (.let₁ (.op false (.pair (.bv 1) (.bv 4))) (.br 1 (.bv 0))))

private def build := compileCaptured sig inputs packets outputs source
private def built : CaptureCompiled sig inputs packets outputs source := build.get (by decide +kernel)

example : inferSlots source = [1] := rfl
example : built.checked.shape.count = 7 := by decide +kernel

private def rowMatches (i : Fin (1 + built.checked.shape.count)) (expected : Region Bool) : Bool :=
  let packed := built.checked.publicReadback
  (commonRow (1 + built.checked.shape.count + 2)
    (packed.packed.target.block (i.cast packed.provenance.count)).erase expected).isSome

example : rowMatches 0 (.br 1 (.var 0)) = true := by decide +kernel
example : rowMatches 1 (.let₂ (.var 0) (.case (.var 1)
    (.br 2 (.pair (.pair (.pair (.var 3) (.var 2)) (.var 1)) (.var 0)))
    (.case (.var 0) (.br 9 (.var 1))
      (.br 6 (.pair (.pair (.pair (.pair (.var 4) (.var 3)) (.var 2)) (.var 1)) (.var 0)))))) = true :=
  by decide +kernel
example : rowMatches 2 (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1)
    (.let₁ (.op false (.pair (.var 4) (.var 2))) (.br 3 (.pair (.var 7) (.var 0))))))) = true :=
  by decide +kernel
example : rowMatches 3 (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1)
    (.br 4 (.pair (.pair (.pair (.pair (.var 1) (.var 0)) (.var 2)) (.var 4)) (.var 6))))))) = true :=
  by decide +kernel
example : rowMatches 4 (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1)
    (.let₁ (.op true (.pair (.var 6) (.var 2))) (.br 5 (.pair (.var 9) (.var 0)))))))) = true :=
  by decide +kernel
example : rowMatches 5 (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1)
    (.br 0 (.pair (.var 8) (.var 2)))))))) = true := by decide +kernel
example : rowMatches 6 (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1)
    (.let₁ (.op false (.pair (.var 4) (.var 2))) (.br 7 (.pair (.var 9) (.var 0)))))))) = true :=
  by decide +kernel
example : rowMatches 7 (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1)
    (.br 8 (.var 8))))))) = true := by decide +kernel

private def first : Denote bit := .inl ⟨⟩
private def second : Denote bit := .inr ⟨⟩
private def env (initial : Denote control) : Env Atom := fun i =>
  if i = 0 then control.encode initial else bit.encode second
private def key (op : Bool) (input : Denote bit) : sig.Request := ⟨op, (input, second)⟩

private noncomputable def step (initial : Denote control) (state : BlockInput Atom 1) :
    Tree Events (Transfer Atom ⊕ BlockInput Atom 1) := blockStep sig.primitive source (env initial) state

private theorem request_tree (req : sig.Request) :
    sig.primitive req.1 ((sig.argument req.1).encode req.2) =
      vis (.ask req) (fun reply : sig.Reply req => pure ((sig.reply req.1).encode reply)) := by
  cases req with
  | mk op arg =>
    unfold PrimitiveSignature.primitive
    rw [Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PacketType.decode_encode]

private theorem row : (source.block 0).erase = .case (.var 0)
    (.let₁ (.op false (.pair (.var 0) (.var 3)))
      (.let₁ (.op true (.pair (.var 0) (.var 4))) (.br 0 (.var 0))))
    (.case (.var 0) (.br 2 (.var 1))
      (.let₁ (.op false (.pair (.var 1) (.var 4))) (.br 1 (.var 0)))) := rfl

private theorem left_visit (initial : Denote control) (input : Denote bit) :
    iter (step initial) (0, control.encode (.inl input)) =
      vis (.ask (key false input)) fun firstReply : sig.Reply (key false input) =>
        vis (.ask (key true firstReply)) fun secondReply : sig.Reply (key true firstReply) =>
          iter (step initial) (0, control.encode secondReply) := by
  rw [congrFun (iterate_fixpoint (step initial)) (0, control.encode (.inl input))]
  simp only [step, blockStep, transfer, row, region, LambdaSSA.Semantics.Interaction.term,
    LambdaSSA.Semantics.extend_zero, PacketType.encode, map_eq_pure_bind, bind_assoc, pure_bind]
  let firstKey := key false input
  change (sig.primitive firstKey.1 ((sig.argument firstKey.1).encode firstKey.2) >>= _) = _
  rw [request_tree firstKey, vis_bind]
  simp only [pure_bind]
  apply congrArg (vis (E := Events) (.ask firstKey))
  funext reply
  let nextKey := key true reply
  change (sig.primitive nextKey.1 ((sig.argument nextKey.1).encode nextKey.2) >>= _) = _
  rw [request_tree nextKey, vis_bind]
  simp [splitTransfer]
  rfl

private theorem bypass_visit (initial : Denote control) :
    iter (step initial) (0, control.encode (.inr first)) = pure (1, bit.encode first) := by
  rw [congrFun (iterate_fixpoint (step initial)) (0, control.encode (.inr first))]
  simp [step, blockStep, transfer, row, region, LambdaSSA.Semantics.Interaction.term, PacketType.encode, first,
    splitTransfer]

private theorem right_visit (initial : Denote control) :
    iter (step initial) (0, control.encode (.inr second)) =
      vis (.ask (key false second)) fun reply : sig.Reply (key false second) => pure (0, bit.encode reply) := by
  rw [congrFun (iterate_fixpoint (step initial)) (0, control.encode (.inr second))]
  simp only [step, blockStep, transfer, row, region, LambdaSSA.Semantics.Interaction.term,
    LambdaSSA.Semantics.extend_zero, PacketType.encode, second, map_eq_pure_bind, bind_assoc, pure_bind]
  let rightKey := key false second
  change (sig.primitive rightKey.1 ((sig.argument rightKey.1).encode rightKey.2) >>= _) = _
  rw [request_tree rightKey, vis_bind]
  simp [splitTransfer]
  rfl

private noncomputable def written (initial : Denote control) : Tree Events (Transfer Atom) :=
  resultCodec id <$> (region sig.primitive (env initial) source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out))

private theorem codec_id (val : Value Atom) : valueCodec id val = val := by
  induction val <;> simp_all only [valueCodec, id_eq]

theorem packed_agrees (result : CaptureCompiled sig inputs packets outputs source) (initial : Denote control) :
    written initial = result.checked.publicReadback.packed.observe (fun _ => .unit) (result.inputRecord id (env initial)) := by
  have primitives : PrimitivesAgree sig.primitive sig.primitive id := by
    intro op val
    rw [codec_id, show valueCodec (id : Atom → Atom) = id from funext codec_id, id_map]
  exact result.public_run (env initial) (fun _ => .unit) id primitives

private theorem written_run (initial : Denote control) :
    written initial = (iter (step initial) (0, control.encode initial) >>= fun out =>
      pure (resultCodec id (FiniteCFG.packedTreeOutput out))) := by
  have start : region sig.primitive (env initial) source.erase = iter (step initial) (0, control.encode initial) := by
    have entry : source.entry.erase = .br 0 (.var 0) := rfl
    simp only [FiniteCFG.erase, region, entry, LambdaSSA.Semantics.Interaction.term, pure_bind]
    have seed : splitTransfer 1 (0, env initial 0) = .inr (0, control.encode initial) := rfl
    rw [seed, Sum.elim_inr]
    have steps : (fun p : BlockInput Atom 1 => region sig.primitive (extend (env initial) p.2)
        (source.block p.1).erase >>= fun out => pure (splitTransfer 1 out)) = step initial := by
      funext p
      simp only [step, blockStep, transfer, map_eq_pure_bind]
    exact congrFun (congrArg iter steps) (0, control.encode initial)
  simp only [written, start, map_eq_pure_bind, bind_assoc, pure_bind]

private def result (port : Nat) (payload : Denote bit) : Transfer Atom :=
  FiniteCFG.packedTreeOutput (port, bit.encode payload)

private def revisitTrace : Trace Events (Transfer Atom) :=
  .exchange (.ask (key false first)) second
    (.exchange (.ask (key true second)) (.inl second)
      (.exchange (.ask (key false second)) first
        (.exchange (.ask (key true first)) (.inr first) (.result (result 1 first)))))

theorem packed_revisit :
    HasTrace (built.checked.publicReadback.packed.observe (fun _ => .unit)
      (built.inputRecord id (env (.inl first)))) revisitTrace := by
  rw [← packed_agrees built (.inl first), written_run (.inl first), left_visit (.inl first) first]
  unfold revisitTrace
  simp only [vis_bind]
  erw [hasTrace_vis_exchange_iff]
  erw [hasTrace_vis_exchange_iff]
  change HasTrace (iter (step (.inl first)) (0, control.encode (.inl second)) >>= _) _
  rw [left_visit (.inl first) second, vis_bind]
  erw [hasTrace_vis_exchange_iff]
  rw [vis_bind]
  erw [hasTrace_vis_exchange_iff]
  rw [bypass_visit (.inl first), pure_bind]
  simp only [resultCodec, codec_id, result]
  exact out_ret _

theorem packed_bypass :
    HasTrace (built.checked.publicReadback.packed.observe (fun _ => .unit)
      (built.inputRecord id (env (.inr first)))) (.result (result 1 first)) := by
  rw [← packed_agrees built (.inr first), written_run (.inr first), bypass_visit (.inr first), pure_bind]
  simp only [resultCodec, codec_id, result]
  exact out_ret _

theorem packed_right :
    HasTrace (built.checked.publicReadback.packed.observe (fun _ => .unit)
      (built.inputRecord id (env (.inr second))))
      (.exchange (.ask (key false second)) first (.result (result 0 first))) := by
  rw [← packed_agrees built (.inr second), written_run (.inr second), right_visit (.inr second), vis_bind]
  erw [hasTrace_vis_exchange_iff]
  simp only [pure_bind, resultCodec, codec_id, result]
  exact out_ret _

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.BranchTransferExamples
