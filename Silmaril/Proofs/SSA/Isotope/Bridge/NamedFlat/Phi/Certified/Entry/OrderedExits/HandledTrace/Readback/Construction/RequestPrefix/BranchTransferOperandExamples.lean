module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Capture.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.BranchTransferOperandExamples

open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (BlockInput Transfer region splitTransfer)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree Trace HasTrace vis iterate_fixpoint vis_bind hasTrace_vis_exchange_iff out_ret)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom Denote PacketType PrimitiveSignature)
open NamedFlat.Capture.Carry (inferSlots packetTypesList)
open EffectfulEntry.Multiple.Computed.Block.Graph (readTreeAt)
open EffectfulEntry.Multiple.Computed.Block.Graph.Capture (prepared)
open EffectfulEntry.Multiple.Computed.Block.Graph.Capture renaming compile → compileCaptured, Compiled → CaptureCompiled

private abbrev bit : PacketType := .coprod .unit .unit
private abbrev control : PacketType := .coprod bit (.coprod bit bit)

private abbrev sig : PrimitiveSignature (Fin 3) :=
  ⟨fun _ => .product bit bit, fun op => if op.val = 1 then control else bit⟩
private abbrev Events := Event sig.Request sig.Reply

private def inputs : BoundCtx PacketType 2 := .snoc (.snoc .nil bit) control
private def packets (_ : Fin 1) : PacketType := control
private def outputs (_ : Fin 2) : PacketType := bit

/-- The left arm computes the original backedge packet. On the right,
an inner case chooses between computing a return packet and returning
its payload directly at a different ordered exit. -/
private def source : FiniteCFG (Fin 3) 1 2 2 where
  entry := .br 0 (.bv 0)
  block _ := .case (.bv 0)
    (.br 0 (.op 1 (.pair (.op 0 (.pair (.bv 0) (.bv 3))) (.bv 3))))
    (.case (.bv 0)
      (.br 2 (.op 2 (.pair (.op 0 (.pair (.bv 0) (.bv 4))) (.bv 4))))
      (.br 1 (.bv 0)))

private def build := compileCaptured sig inputs packets outputs source
private def built : CaptureCompiled sig inputs packets outputs source := build.get (by decide +kernel)

example : inferSlots source = [1] := rfl

-- The exact continuation reader rejects the computed transfers before scheduling.
example :
    let carried := packetTypesList packets inputs (inferSlots source)
    let row := ((prepared source).block 0).erase
    (readTreeAt sig carried outputs (carried 0) row row (.inl rfl)).isNone = true :=
  by decide +kernel

example : built.checked.shape.count = 9 := by decide +kernel

private def rowMatches (i : Fin (1 + built.checked.shape.count)) (expected : Region (Fin 3)) : Bool :=
  let packed := built.checked.publicReadback
  (commonRow (1 + built.checked.shape.count + 2)
    (packed.packed.target.block (i.cast packed.provenance.count)).erase expected).isSome

-- The silent leaf returns at exit zero without entering either request schedule.
example : rowMatches 1 (.let₂ (.var 0) (.case (.var 1)
    (.br 2 (.pair (.pair (.pair (.var 3) (.var 2)) (.var 1)) (.var 0)))
    (.case (.var 0)
      (.br 6 (.pair (.pair (.pair (.pair (.var 4) (.var 3)) (.var 2)) (.var 1)) (.var 0)))
      (.br 10 (.var 0))))) = true := by decide +kernel

-- The backedge carries the new packet and the older capture.
example : rowMatches 5 (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1)
    (.let₂ (.var 1) (.let₂ (.var 1) (.br 0 (.pair (.var 8) (.var 2)))))))) = true := by decide +kernel

-- The computed return sends only the reply at exit one.
example : rowMatches 9 (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1)
    (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1) (.br 11 (.var 10)))))))) = true := by decide +kernel

private def first : Denote bit := .inl ⟨⟩
private def second : Denote bit := .inr ⟨⟩
private def env (initial : Denote control) : Env Atom := fun i =>
  if i = 0 then control.encode initial else bit.encode second
private def innerKey (input : Denote bit) : sig.Request := ⟨0, (input, second)⟩
private def backedgeKey (input : Denote bit) : sig.Request := ⟨1, (input, second)⟩
private def returnKey (input : Denote bit) : sig.Request := ⟨2, (input, second)⟩

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
    (.br 0 (.op 1 (.pair (.op 0 (.pair (.var 0) (.var 3))) (.var 3))))
    (.case (.var 0)
      (.br 2 (.op 2 (.pair (.op 0 (.pair (.var 0) (.var 4))) (.var 4))))
      (.br 1 (.var 0))) := rfl

private theorem visit (initial current : Denote control) :
    iter (step initial) (0, control.encode current) =
      match current with
      | .inl payload =>
        vis (.ask (innerKey payload)) fun reply : sig.Reply (innerKey payload) =>
          vis (.ask (backedgeKey reply)) fun next : sig.Reply (backedgeKey reply) =>
            iter (step initial) (0, control.encode next)
      | .inr (.inl payload) =>
        vis (.ask (innerKey payload)) fun reply : sig.Reply (innerKey payload) =>
          vis (.ask (returnKey reply)) fun out : sig.Reply (returnKey reply) =>
            pure (1, bit.encode out)
      | .inr (.inr payload) => pure (0, bit.encode payload) := by
  rw [congrFun (iterate_fixpoint (step initial)) (0, control.encode current)]
  cases current with
  | inl payload =>
    have packet : extend (env initial) (control.encode (.inl payload)) 0 = .inl (bit.encode payload) := rfl
    simp only [step, blockStep, transfer, row, region, LambdaSSA.Semantics.Interaction.term,
      map_eq_pure_bind, packet, bind_assoc, pure_bind]
    let key := innerKey payload
    change (sig.primitive key.1 ((sig.argument key.1).encode key.2) >>= _) = _
    rw [request_tree key, vis_bind]
    simp only [pure_bind]
    apply congrArg (vis (E := Events) (.ask key))
    funext reply
    let next := backedgeKey reply
    change (sig.primitive next.1 ((sig.argument next.1).encode next.2) >>= _) = _
    rw [request_tree next, vis_bind]
    simp [splitTransfer]
    rfl
  | inr tag =>
    cases tag with
    | inl payload =>
      have packet : extend (env initial) (control.encode (.inr (.inl payload))) 0 =
          .inr (.inl (bit.encode payload)) := rfl
      have inner : extend (extend (env initial) (control.encode (.inr (.inl payload))))
          (.inl (bit.encode payload)) 0 = .inl (bit.encode payload) := rfl
      simp only [step, blockStep, transfer, row, region, LambdaSSA.Semantics.Interaction.term,
        map_eq_pure_bind, packet, inner, bind_assoc, pure_bind]
      let key := innerKey payload
      change (sig.primitive key.1 ((sig.argument key.1).encode key.2) >>= _) = _
      rw [request_tree key, vis_bind]
      simp only [pure_bind]
      apply congrArg (vis (E := Events) (.ask key))
      funext reply
      let next := returnKey reply
      change (sig.primitive next.1 ((sig.argument next.1).encode next.2) >>= _) = _
      rw [request_tree next, vis_bind]
      simp [splitTransfer]
      rfl
    | inr payload =>
      have packet : extend (env initial) (control.encode (.inr (.inr payload))) 0 =
          .inr (.inr (bit.encode payload)) := rfl
      have inner : extend (extend (env initial) (control.encode (.inr (.inr payload))))
          (.inr (bit.encode payload)) 0 = .inr (bit.encode payload) := rfl
      simp only [step, blockStep, transfer, row, region, LambdaSSA.Semantics.Interaction.term,
        map_eq_pure_bind, packet, inner, bind_assoc, pure_bind]
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
  .exchange (.ask (innerKey first)) second
    (.exchange (.ask (backedgeKey second)) (.inl second)
      (.exchange (.ask (innerKey second)) first
        (.exchange (.ask (backedgeKey first)) (.inr (.inl first))
          (.exchange (.ask (innerKey first)) second
            (.exchange (.ask (returnKey second)) first (.result (result 1 first)))))))

theorem packed_revisit :
    HasTrace (built.checked.publicReadback.packed.observe (fun _ => .unit)
      (built.inputRecord id (env (.inl first)))) revisitTrace := by
  rw [← packed_agrees built (.inl first), written_run (.inl first), visit (.inl first) (.inl first), vis_bind]
  unfold revisitTrace
  erw [hasTrace_vis_exchange_iff]
  rw [vis_bind]
  erw [hasTrace_vis_exchange_iff]
  rw [visit (.inl first) (.inl second), vis_bind]
  erw [hasTrace_vis_exchange_iff]
  rw [vis_bind]
  erw [hasTrace_vis_exchange_iff]
  rw [visit (.inl first) (.inr (.inl first)), vis_bind]
  erw [hasTrace_vis_exchange_iff]
  rw [vis_bind]
  erw [hasTrace_vis_exchange_iff]
  simp only [pure_bind, resultCodec, codec_id, result]
  exact out_ret _

theorem packed_direct :
    built.checked.publicReadback.packed.observe (fun _ => .unit)
      (built.inputRecord id (env (.inr (.inr first)))) = pure (result 0 first) := by
  rw [← packed_agrees built (.inr (.inr first)), written_run (.inr (.inr first)),
    visit (.inr (.inr first)) (.inr (.inr first))]
  simp only [pure_bind, resultCodec, codec_id, result]

example : result 0 first ≠ result 1 first := by decide

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.BranchTransferOperandExamples
