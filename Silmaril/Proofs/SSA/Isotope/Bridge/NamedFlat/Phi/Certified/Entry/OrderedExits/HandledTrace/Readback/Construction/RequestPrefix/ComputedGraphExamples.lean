module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Capture.Defs
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.ComputedGraphExamples

open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (BlockInput Transfer region splitTransfer)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree Trace HasTrace vis iterate_fixpoint vis_bind hasTrace_vis_exchange_iff out_ret)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom Denote PacketType PrimitiveSignature)
open EffectfulEntry.Multiple.Computed.Block.Graph renaming compile → compileGraph, Compiled → GraphCompiled

private abbrev bit : PacketType := .coprod .unit .unit
private abbrev control : PacketType := .coprod bit bit
private abbrev packet : PacketType := .product control bit

private abbrev sig : PrimitiveSignature Bool :=
  ⟨fun _ => packet, fun op => if op then .product control .unit else control⟩
private abbrev Events := Event sig.Request sig.Reply

private def inputs : BoundCtx PacketType 2 := .snoc (.snoc .nil bit) control
private def outputs (i : Fin 2) : PacketType := if i.val = 0 then .unit else .product bit bit

/-- Both computed transfers send an updated control and the carried
capture along original edges. The third block routes the reply either
back to the first computed block or out through the second exit. -/
private def source : FiniteCFG Bool 3 2 2 where
  entry := .br 2 (.pair (.bv 0) (.bv 1))
  block i := if i.val = 0 then
    .br 1 (.let₂ (.bv 0) (.pair (.op false (.pair (.bv 1) (.bv 0))) (.bv 0)))
  else if i.val = 1 then
    .br 2 (.let₂ (.op true (.bv 0)) (.let₂ (.bv 2) (.pair (.bv 3) (.bv 0))))
  else .let₂ (.bv 0) (.case (.bv 1) (.br 0 (.pair (.bv 2) (.bv 1))) (.br 4 (.pair (.bv 0) (.bv 1))))

private def build := compileGraph sig inputs (fun _ => packet) outputs source
private def built : GraphCompiled sig inputs (fun _ => packet) outputs source :=
  build.get (by decide +kernel)

private def rowMatches (i : Fin (3 + built.shape.count)) (expected : Region Bool) : Bool :=
  (commonRow (3 + built.shape.count + 2)
    (built.publicReadback.packed.target.block (i.cast built.publicReadback.provenance.count)).erase expected).isSome

example : built.shape.count = 7 := by decide +kernel
example : (built.shape.row 0).count = 3 ∧ (built.shape.row 1).count = 4 ∧ (built.shape.row 2).count = 0 :=
  by decide +kernel
example : built.emitted.code.entry.erase = source.entry.erase := built.emitted.entry_eq
example : rowMatches 0 (.br 3 (.var 0)) = true := by decide +kernel
example : rowMatches 1 (.br 6 (.var 0)) = true := by decide +kernel
example : rowMatches 2 (.let₂ (.var 0) (.case (.var 1)
    (.br 0 (.pair (.var 2) (.var 1))) (.br 11 (.pair (.var 0) (.var 1))))) = true := by decide +kernel
example : rowMatches 3 (.let₂ (.var 0) (.br 4 (.pair (.pair (.var 2) (.var 1)) (.var 0)))) = true :=
  by decide +kernel
example : rowMatches 4 (.let₂ (.var 0) (.let₂ (.var 1)
    (.let₁ (.op false (.pair (.var 0) (.var 2))) (.br 5 (.pair (.var 5) (.var 0)))))) = true := by decide +kernel
example : rowMatches 5 (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1)
    (.br 1 (.pair (.var 4) (.var 2)))))) = true := by decide +kernel
example : rowMatches 6 (.let₁ (.op true (.var 0)) (.br 7 (.pair (.var 1) (.var 0)))) = true := by decide +kernel
example : rowMatches 7 (.let₂ (.var 0) (.br 8 (.pair (.var 1) (.var 0)))) = true := by decide +kernel
example : rowMatches 8 (.let₂ (.var 0) (.let₂ (.var 0)
    (.br 9 (.pair (.pair (.pair (.var 3) (.var 2)) (.var 1)) (.var 0))))) = true := by decide +kernel
example : rowMatches 9 (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1)
    (.br 2 (.pair (.var 4) (.var 0))))))) = true := by decide +kernel

private def twoRequestRow : LambdaSSA.Flat Bool 5 3 :=
  .let₁ (.op false (.bv 0)) (.let₁ (.op false (.bv 1)) (.br 1 (.bv 2)))

private def twoRequests : FiniteCFG Bool 3 2 2 :=
  { source with block := fun i => if i.val = 0 then twoRequestRow else source.block i }

-- Both requests in this original case arm now admit.
private def branchingRow : LambdaSSA.Flat Bool 5 3 :=
  .let₂ (.bv 0) (.case (.bv 1)
    (.let₁ (.op false (.bv 3)) (.let₁ (.op false (.bv 4)) (.br 1 (.bv 5))))
    (.br 2 (.bv 3)))

private def branching : FiniteCFG Bool 3 2 2 :=
  { source with block := fun i => if i.val = 0 then branchingRow else source.block i }

private def ambientRead : FiniteCFG Bool 3 2 2 :=
  { source with block := fun i => if i.val = 0 then .br 1 (.pair (.bv 1) (.bv 2)) else source.block i }

example : (compileGraph sig inputs (fun _ => packet) outputs twoRequests).isSome = true := by decide +kernel
example : (compileGraph sig inputs (fun _ => packet) outputs branching).isSome = true := by decide +kernel
example : (EffectfulEntry.Multiple.Computed.Block.Graph.Capture.compile sig inputs
    (fun _ => packet) outputs branching).isSome = true := by decide +kernel

private def effectfulTestRow : LambdaSSA.Flat Bool 5 3 :=
  .case (.op false (.bv 0)) (.br 1 (.bv 1)) (.br 2 (.bv 1))

private def effectfulTest : FiniteCFG Bool 3 2 2 :=
  { source with block := fun i => if i.val = 0 then effectfulTestRow else source.block i }

example : let _ := sig.typing; NamedFlat.check effectfulTest inputs (fun _ => packet) outputs = true := rfl
example : (compileGraph sig inputs (fun _ => packet) outputs effectfulTest).isSome = true := by decide +kernel
example : (EffectfulEntry.Multiple.Computed.Block.Graph.Capture.compile sig inputs
    (fun _ => packet) outputs effectfulTest).isSome = true := by decide +kernel

example : let _ := sig.typing; NamedFlat.check ambientRead inputs (fun _ => packet) outputs = true := rfl
example : (compileGraph sig inputs (fun _ => packet) outputs ambientRead).isNone = true := rfl

example : (EffectfulEntry.Multiple.Computed.Block.Graph.Capture.compile sig inputs
    (fun _ => packet) outputs ambientRead).isSome = true := by decide +kernel

private def first : Denote bit := .inl ⟨⟩
private def second : Denote bit := .inr ⟨⟩

private def value (current : Denote control) : Value Atom := packet.encode (current, second)
private def env : Env Atom := fun i => if i = 0 then control.encode (.inl first) else bit.encode second
private def record : Env Atom := fun _ => value (.inl first)
private def key (op : Bool) (current : Denote control) : sig.Request := ⟨op, (current, second)⟩

private noncomputable def step (state : BlockInput Atom 3) : Tree Events (Transfer Atom ⊕ BlockInput Atom 3) :=
  blockStep sig.primitive source env state

private theorem request_tree (req : sig.Request) :
    sig.primitive req.1 ((sig.argument req.1).encode req.2) =
      vis (.ask req) (fun reply : sig.Reply req => pure ((sig.reply req.1).encode reply)) := by
  cases req with
  | mk op arg =>
    unfold PrimitiveSignature.primitive
    rw [Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PacketType.decode_encode]

private theorem first_visit (current : Denote control) :
    iter step (0, value current) =
      vis (.ask (key false current)) (fun reply : sig.Reply (key false current) => iter step (1, value reply)) := by
  rw [congrFun (iterate_fixpoint step) (0, value current)]
  have row : (source.block 0).erase =
      .br 1 (.let₂ (.var 0) (.pair (.op false (.pair (.var 1) (.var 0))) (.var 0))) := rfl
  simp only [step, blockStep, transfer, row, region, LambdaSSA.Semantics.Interaction.term,
    map_eq_pure_bind, bind_assoc, pure_bind]
  have incoming : value current = .pair (control.encode current) (bit.encode second) := rfl
  simp only [LambdaSSA.Semantics.extend_zero, incoming, bind_assoc, pure_bind]
  change (sig.primitive (key false current).1 ((sig.argument (key false current).1).encode (key false current).2) >>= _) = _
  rw [request_tree (key false current), vis_bind]
  simp only [pure_bind]
  apply congrArg (vis (E := Events) (.ask (key false current)))
  funext reply
  have encoded : (sig.reply (key false current).1).encode reply = control.encode reply := rfl
  simp [encoded, value, PacketType.encode, splitTransfer]

private theorem second_visit (current : Denote control) :
    iter step (1, value current) =
      vis (.ask (key true current)) (fun reply : sig.Reply (key true current) => iter step (2, value reply.1)) := by
  rw [congrFun (iterate_fixpoint step) (1, value current)]
  have row : (source.block 1).erase =
      .br 2 (.let₂ (.op true (.var 0)) (.let₂ (.var 2) (.pair (.var 3) (.var 0)))) := rfl
  simp only [step, blockStep, transfer, row, region, LambdaSSA.Semantics.Interaction.term,
    map_eq_pure_bind, bind_assoc, pure_bind]
  change (sig.primitive (key true current).1 ((sig.argument (key true current).1).encode (key true current).2) >>= _) = _
  rw [request_tree (key true current), vis_bind]
  simp only [pure_bind]
  apply congrArg (vis (E := Events) (.ask (key true current)))
  funext reply
  rcases reply with ⟨next, ignored⟩
  have encoded : (sig.reply (key true current).1).encode (next, ignored) =
      .pair (control.encode next) .unit := rfl
  simp [encoded, value, PacketType.encode, splitTransfer]

private theorem route_row : (source.block 2).erase =
    .let₂ (.var 0) (.case (.var 1) (.br 0 (.pair (.var 2) (.var 1))) (.br 4 (.pair (.var 0) (.var 1)))) := rfl

private theorem repeat_visit (current : Denote bit) :
    iter step (2, value (.inl current)) = iter step (0, value (.inl current)) := by
  rw [congrFun (iterate_fixpoint step) (2, value (.inl current))]
  simp [step, blockStep, transfer, route_row, region, LambdaSSA.Semantics.Interaction.term,
    value, PacketType.encode, splitTransfer]

private theorem return_visit (payload : Denote bit) :
    iter step (2, value (.inr payload)) = pure (1, .pair (bit.encode payload) (bit.encode second)) := by
  rw [congrFun (iterate_fixpoint step) (2, value (.inr payload))]
  simp [step, blockStep, transfer, route_row, region, LambdaSSA.Semantics.Interaction.term,
    value, PacketType.encode, splitTransfer]

private noncomputable def written : Tree Events (Transfer Atom) :=
  resultCodec id <$> (region sig.primitive env source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out))

private theorem codec_id (val : Value Atom) : valueCodec id val = val := by
  induction val <;> simp_all only [valueCodec, id_eq]

private theorem seed_value (result : GraphCompiled sig inputs (fun _ => packet) outputs source) :
    packetValue env result.publicReadback.provenance.seed = value (.inl first) := by
  have writtenEntry : source.entry.erase = .br 2 (.pair (.var 0) (.var 1)) := rfl
  have seed := (Region.br.inj
    (result.publicReadback.provenance.sourceEntry.symm.trans (result.emitted.entry_eq.trans writtenEntry))).2
  apply (Silmaril.Elgot.ITree.ret_inj (E := Events)).mp
  change (pure _ : Tree Events _) = pure _
  rw [← packet_term_tree sig.primitive env, seed]
  simp only [LambdaSSA.Semantics.Interaction.term, pure_bind]
  rfl

theorem packed_agrees (result : GraphCompiled sig inputs (fun _ => packet) outputs source) :
    written = result.publicReadback.packed.observe env record := by
  have primitives : PrimitivesAgree sig.primitive sig.primitive id := by
    intro op val
    rw [codec_id, show valueCodec (id : Atom → Atom) = id from funext codec_id, id_map]
  exact result.public_run env env record id primitives (by rw [seed_value, codec_id]; rfl)

private def twice : Trace Events (Transfer Atom) :=
  .exchange (.ask (key false (.inl first))) (.inl second)
    (.exchange (.ask (key true (.inl second))) (.inl second, ⟨⟩)
      (.exchange (.ask (key false (.inl second))) (.inl first)
        (.exchange (.ask (key true (.inl first))) (.inr first, ⟨⟩)
          (.result (FiniteCFG.packedTreeOutput (1, .pair (bit.encode first) (bit.encode second)))))))

theorem packed_two_rounds : HasTrace (built.publicReadback.packed.observe env record) twice := by
  rw [← packed_agrees built]
  unfold written twice
  have start : region sig.primitive env source.erase = iter step (2, value (.inl first)) := by
    have entry : source.entry.erase = .br 2 (.pair (.var 0) (.var 1)) := rfl
    simp only [FiniteCFG.erase, region, entry, LambdaSSA.Semantics.Interaction.term, pure_bind]
    have seed : splitTransfer 3 (2, .pair (env 0) (env 1)) = .inr (2, value (.inl first)) := rfl
    rw [seed, Sum.elim_inr]
    have steps : (fun p : BlockInput Atom 3 => region sig.primitive (extend env p.2)
        (source.block p.1).erase >>= fun out => pure (splitTransfer 3 out)) = step := by
      funext p
      simp only [step, blockStep, transfer, map_eq_pure_bind]
    exact congrFun (congrArg iter steps) (2, value (.inl first))
  rw [start, repeat_visit first, first_visit (.inl first)]
  simp only [map_eq_pure_bind, bind_assoc, vis_bind]
  erw [hasTrace_vis_exchange_iff]
  change HasTrace (iter step (1, value (.inl second)) >>= _) _
  rw [second_visit (.inl second), vis_bind]
  erw [hasTrace_vis_exchange_iff]
  change HasTrace (iter step (2, value (.inl second)) >>= _) _
  rw [repeat_visit second, first_visit (.inl second), vis_bind]
  erw [hasTrace_vis_exchange_iff]
  rw [second_visit (.inl first), vis_bind]
  erw [hasTrace_vis_exchange_iff]
  change HasTrace (iter step (2, value (.inr first)) >>= _) _
  rw [return_visit first, pure_bind]
  simp only [resultCodec, codec_id, pure_bind]
  exact out_ret _

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.ComputedGraphExamples
