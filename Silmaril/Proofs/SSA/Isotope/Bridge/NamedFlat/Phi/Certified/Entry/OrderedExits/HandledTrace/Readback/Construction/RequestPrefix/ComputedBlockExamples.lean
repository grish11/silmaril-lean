module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.ComputedBlockExamples

open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (BlockInput Transfer region splitTransfer)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree Trace HasTrace vis iterate_fixpoint vis_bind hasTrace_vis_exchange_iff out_ret)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom Denote PacketType PrimitiveSignature)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block
  renaming compile → compileBlock, Compiled → BlockCompiled, read → readBlock

private abbrev bit : PacketType := .coprod .unit .unit
private abbrev control : PacketType := .coprod bit bit
private abbrev packet : PacketType := .product control bit

private abbrev sig : PrimitiveSignature Unit :=
  ⟨fun _ => packet, fun _ => .product control .unit⟩
private abbrev Events := Event sig.Request sig.Reply

private def inputs : BoundCtx PacketType 2 := .snoc (.snoc .nil bit) control
private def outputs (i : Fin 2) : PacketType := if i.val = 0 then .unit else .product bit bit

/-- Block zero computes its transfer from a pair-valued request and the
current packet. Block one is the original predecessor on the first visit
and every repeat, with the updated control and the original carry. -/
private def source : FiniteCFG Unit 2 2 2 where
  entry := .br 1 (.pair (.bv 0) (.bv 1))
  block i := if i.val = 0 then
    .br 1 (.let₂ (.op () (.bv 0)) (.let₂ (.bv 2) (.pair (.bv 3) (.bv 0))))
  else .let₂ (.bv 0) (.case (.bv 1) (.br 0 (.pair (.bv 2) (.bv 1))) (.br 3 (.pair (.bv 0) (.bv 1))))

private def build := compileBlock sig inputs (fun _ => packet) outputs source 0
private def built : BlockCompiled sig inputs (fun _ => packet) outputs source :=
  build.get (by decide +kernel)

private def rowMatches (i : Fin (2 + built.shape.count)) (expected : Region Unit) : Bool :=
  (commonRow (2 + built.shape.count + 2)
    (built.publicReadback.packed.target.block (i.cast built.publicReadback.provenance.count)).erase expected).isSome

example : built.shape.count = 4 := by decide +kernel
example : built.emitted.code.entry.erase = source.entry.erase := built.emitted.entry_eq
example : rowMatches 0 (.br 2 (.var 0)) = true := by decide +kernel
example : rowMatches 1 (.let₂ (.var 0) (.case (.var 1)
    (.br 0 (.pair (.var 2) (.var 1))) (.br 7 (.pair (.var 0) (.var 1))))) = true := by decide +kernel
example : rowMatches 2 (.let₁ (.op () (.var 0)) (.br 3 (.pair (.var 1) (.var 0)))) = true := by decide +kernel

example : rowMatches 3 (.let₂ (.var 0) (.br 4 (.pair (.var 1) (.var 0)))) = true := by decide +kernel
example : rowMatches 4 (.let₂ (.var 0) (.let₂ (.var 0)
    (.br 5 (.pair (.pair (.pair (.var 3) (.var 2)) (.var 1)) (.var 0))))) = true := by decide +kernel
example : rowMatches 5 (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1)
    (.br 1 (.pair (.var 4) (.var 0))))))) = true := by decide +kernel

-- A well-typed ambient capture read is outside the packet-local boundary.
private def ambientRead : FiniteCFG Unit 2 2 2 :=
  { source with block := fun i => if i.val = 0 then .br 1 (.pair (.bv 1) (.bv 2)) else source.block i }

example : let _ := sig.typing; NamedFlat.check ambientRead inputs (fun _ => packet) outputs = true := rfl

example : (readBlock sig (fun _ => packet) outputs ambientRead 0).isNone = true := rfl

private def first : Denote bit := .inl ⟨⟩
private def second : Denote bit := .inr ⟨⟩
private def capture : Denote bit := second

private def value (current : Denote control) : Value Atom := packet.encode (current, capture)
private def env : Env Atom := fun i => if i = 0 then control.encode (.inl first) else bit.encode capture
private def record : Env Atom := fun _ => value (.inl first)
private def key (current : Denote control) : sig.Request := ⟨(), (current, capture)⟩

private noncomputable def step (state : BlockInput Atom 2) : Tree Events (Transfer Atom ⊕ BlockInput Atom 2) :=
  blockStep sig.primitive source env state

private theorem request_tree (req : sig.Request) :
    sig.primitive req.1 ((sig.argument req.1).encode req.2) =
      vis (.ask req) (fun reply : sig.Reply req => pure ((sig.reply req.1).encode reply)) := by
  cases req with
  | mk op arg =>
    unfold PrimitiveSignature.primitive
    rw [Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PacketType.decode_encode]

private theorem visit (current : Denote control) :
    iter step (0, value current) =
      vis (.ask (key current)) (fun reply : sig.Reply (key current) => iter step (1, value reply.1)) := by
  rw [congrFun (iterate_fixpoint step) (0, value current)]
  have row : (source.block 0).erase =
      .br 1 (.let₂ (.op () (.var 0)) (.let₂ (.var 2) (.pair (.var 3) (.var 0)))) := rfl
  simp only [step, blockStep, transfer, row, region, LambdaSSA.Semantics.Interaction.term, map_eq_pure_bind, bind_assoc, pure_bind]
  change (sig.primitive (key current).1 ((sig.argument (key current).1).encode (key current).2) >>= _) = _
  rw [request_tree (key current), vis_bind]
  simp only [pure_bind]
  apply congrArg (vis (E := Events) (.ask (key current)))
  funext reply
  rcases reply with ⟨next, ignored⟩
  simp [value, PacketType.encode, splitTransfer]

private theorem route_row : (source.block 1).erase =
    .let₂ (.var 0) (.case (.var 1) (.br 0 (.pair (.var 2) (.var 1))) (.br 3 (.pair (.var 0) (.var 1)))) := rfl

private theorem repeat_visit (current : Denote bit) :
    iter step (1, value (.inl current)) = iter step (0, value (.inl current)) := by
  rw [congrFun (iterate_fixpoint step) (1, value (.inl current))]
  simp [step, blockStep, transfer, route_row, region, LambdaSSA.Semantics.Interaction.term, value, PacketType.encode, splitTransfer]

private theorem return_visit (payload : Denote bit) :
    iter step (1, value (.inr payload)) = pure (1, .pair (bit.encode payload) (bit.encode capture)) := by
  rw [congrFun (iterate_fixpoint step) (1, value (.inr payload))]
  simp [step, blockStep, transfer, route_row, region, LambdaSSA.Semantics.Interaction.term, value, PacketType.encode, splitTransfer]

private noncomputable def written : Tree Events (Transfer Atom) :=
  resultCodec id <$> (region sig.primitive env source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out))

private theorem codec_id (val : Value Atom) : valueCodec id val = val := by
  induction val <;> simp_all only [valueCodec, id_eq]

private theorem seed_value (result : BlockCompiled sig inputs (fun _ => packet) outputs source) :
    packetValue env result.publicReadback.provenance.seed = value (.inl first) := by
  have writtenEntry : source.entry.erase = .br 1 (.pair (.var 0) (.var 1)) := rfl
  have seed := (Region.br.inj
    (result.publicReadback.provenance.sourceEntry.symm.trans (result.emitted.entry_eq.trans writtenEntry))).2
  apply (Silmaril.Elgot.ITree.ret_inj (E := Events)).mp
  change (pure _ : Tree Events _) = pure _
  rw [← packet_term_tree sig.primitive env, seed]
  simp only [LambdaSSA.Semantics.Interaction.term, pure_bind]
  rfl

theorem packed_agrees (result : BlockCompiled sig inputs (fun _ => packet) outputs source) :
    written = result.publicReadback.packed.observe env record := by
  have primitives : PrimitivesAgree sig.primitive sig.primitive id := by
    intro op val
    rw [codec_id, show valueCodec (id : Atom → Atom) = id from funext codec_id, id_map]
  exact result.public_run env env record id primitives (by rw [seed_value, codec_id]; rfl)

private def twice : Trace Events (Transfer Atom) :=
  .exchange (.ask (key (.inl first))) (.inl second, ⟨⟩)
    (.exchange (.ask (key (.inl second))) (.inr first, ⟨⟩)
      (.result (FiniteCFG.packedTreeOutput (1, .pair (bit.encode first) (bit.encode capture)))))

/-- The first reply changes the key of the next request, which is entered
through the original backedge. The second reply takes the second exit. -/
theorem packed_two_visits : HasTrace (built.publicReadback.packed.observe env record) twice := by
  rw [← packed_agrees built]
  unfold written twice
  have start : region sig.primitive env source.erase = iter step (1, value (.inl first)) := by
    have entry : source.entry.erase = .br 1 (.pair (.var 0) (.var 1)) := rfl
    simp only [FiniteCFG.erase, region, entry, LambdaSSA.Semantics.Interaction.term, pure_bind]
    have seed : splitTransfer 2 (1, .pair (env 0) (env 1)) = .inr (1, value (.inl first)) := rfl
    rw [seed, Sum.elim_inr]
    have steps : (fun p : BlockInput Atom 2 => region sig.primitive (LambdaSSA.Semantics.extend env p.2)
        (source.block p.1).erase >>= fun out => pure (splitTransfer 2 out)) = step := by
      funext p
      simp only [step, blockStep, transfer, map_eq_pure_bind]
    exact congrFun (congrArg iter steps) (1, value (.inl first))
  rw [start, repeat_visit first, visit (.inl first)]
  simp only [map_eq_pure_bind, bind_assoc, vis_bind]
  erw [hasTrace_vis_exchange_iff]
  change HasTrace (iter step (1, value (.inl second)) >>= _) _
  rw [repeat_visit second, visit (.inl second), vis_bind]
  erw [hasTrace_vis_exchange_iff]
  change HasTrace (iter step (1, value (.inr first)) >>= _) _
  rw [return_visit first, pure_bind]
  simp only [resultCodec, codec_id, pure_bind]
  exact out_ret _

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.ComputedBlockExamples
