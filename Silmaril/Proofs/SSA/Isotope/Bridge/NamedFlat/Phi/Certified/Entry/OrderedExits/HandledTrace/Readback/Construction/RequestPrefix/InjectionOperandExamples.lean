module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Native.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.InjectionOperandExamples

open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (BlockInput Transfer region splitTransfer)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree vis iterate_fixpoint vis_bind)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom Denote PacketType PrimitiveSignature)
open EffectfulEntry.Multiple.Computed (readArgument readOperand)
open EffectfulEntry.Multiple.Computed.Native renaming Compiled → Scheduled, compile → compileNative

private abbrev bit : PacketType := .coprod .unit .unit
private abbrev choice : PacketType := .coprod bit bit
private abbrev sig : PrimitiveSignature (Fin 2) :=
  ⟨fun op => if op.val = 0 then bit else choice, fun _ => bit⟩
private abbrev Events := Event sig.Request sig.Reply

private def inputs : BoundCtx PacketType 2 := .snoc (.snoc .nil bit) bit
private def packets (_ : Fin 1) : PacketType := bit
private def outputs (_ : Fin 2) : PacketType := choice

/-- Both branches call the same primitives. The second request receives the
same payload under a different sum tag, and the return uses the written exit. -/
private def source : FiniteCFG (Fin 2) 1 2 2 where
  entry := .br 0 (.bv 0)
  block _ := .case (.bv 0)
    (.let₁ (.op 1 (.inl (.op 0 (.bv 3)))) (.br 1 (.inl (.bv 0))))
    (.let₁ (.op 1 (.inr (.op 0 (.bv 3)))) (.br 2 (.inr (.bv 0))))

private def build := compileNative sig inputs packets outputs source
private def built : Scheduled sig inputs packets outputs source := build.get (by decide +kernel)

-- The checker used by the public path before scheduling injections rejects the written graph.
example : let _ := sig.typing; NamedFlat.check source inputs packets outputs = false := by decide +kernel

-- The unused summand comes from the supplied sum type. Only the right
-- injection below can take the reply of opcode zero at this profile.
example : (readArgument sig [bit] (.coprod .unit bit) (.inl (.op 0 (.var 0)))).isNone = true :=
  by decide +kernel
example : (readArgument sig [bit] (.coprod .unit bit) (.inr (.op 0 (.var 0)))).isSome = true :=
  by decide +kernel
example : (readOperand sig [bit] (.inr (.op 0 (.var 0)))).isNone = true :=
  by decide +kernel

example : built.code.entry = source.entry := by decide +kernel
example : built.code.block 0 = .case (.bv 0)
    (.let₁ (.op 0 (.bv 3)) (.let₁ (.op 1 (.inl (.bv 0))) (.br 1 (.inl (.bv 0)))))
    (.let₁ (.op 0 (.bv 3)) (.let₁ (.op 1 (.inr (.bv 0))) (.br 2 (.inr (.bv 0))))) :=
  by decide +kernel

private def capture : Denote bit := .inr ⟨⟩
private def env (left : Bool) : Env Atom := fun i =>
  if i = 0 then bit.encode (if left then .inl ⟨⟩ else .inr ⟨⟩) else bit.encode capture

private def payloadKey : sig.Request := ⟨0, capture⟩
private def tagged (left : Bool) (payload : Denote bit) : Denote choice :=
  if left then .inl payload else .inr payload
private def consumeKey (left : Bool) (payload : Denote bit) : sig.Request := ⟨1, tagged left payload⟩

private theorem request_tree (req : sig.Request) :
    sig.primitive req.1 ((sig.argument req.1).encode req.2) =
      vis (.ask req) (fun reply : sig.Reply req => pure ((sig.reply req.1).encode reply)) := by
  cases req with
  | mk op arg =>
    unfold PrimitiveSignature.primitive
    rw [Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PacketType.decode_encode]

private def finish (left : Bool) (output : Denote bit) : Transfer Atom :=
  FiniteCFG.packedTreeOutput (if left then 0 else 1, choice.encode (tagged left output))

private noncomputable def expected (left : Bool) : Tree Events (Transfer Atom) :=
  vis (.ask payloadKey) fun reply : sig.Reply payloadKey =>
    vis (.ask (consumeKey left reply)) fun output : sig.Reply (consumeKey left reply) =>
      pure (finish left output)

private theorem source_run (left : Bool) :
    (region sig.primitive (env left) source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      expected left := by
  let step := fun p : BlockInput Atom 1 =>
    region sig.primitive (extend (env left) p.2) (source.block p.1).erase >>= fun out =>
      pure (splitTransfer 1 out)
  have start : region sig.primitive (env left) source.erase = iter step (0, env left 0) := by
    have entry : source.entry.erase = .br 0 (.var 0) := rfl
    simp only [FiniteCFG.erase, region, entry, LambdaSSA.Semantics.Interaction.term, pure_bind]
    rw [show splitTransfer 1 (0, env left 0) = .inr (0, env left 0) from rfl, Sum.elim_inr]
    rfl
  rw [start, congrFun (iterate_fixpoint step) (0, env left 0)]
  have row : (source.block 0).erase = .case (.var 0)
      (.let₁ (.op 1 (.inl (.op 0 (.var 3)))) (.br 1 (.inl (.var 0))))
      (.let₁ (.op 1 (.inr (.op 0 (.var 3)))) (.br 2 (.inr (.var 0)))) := rfl
  have packet : extend (env left) (env left 0) 0 = if left then .inl .unit else .inr .unit := by
    cases left <;> rfl
  cases left <;> simp only [step, row, region, LambdaSSA.Semantics.Interaction.term, packet,
    Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
  all_goals
    change (sig.primitive payloadKey.1 ((sig.argument payloadKey.1).encode payloadKey.2) >>= _) = _
    rw [request_tree payloadKey, vis_bind]
    simp only [pure_bind]
    apply congrArg (vis (E := Events) (.ask payloadKey))
    funext reply
    first
    | change (sig.primitive (consumeKey false reply).1
        ((sig.argument (consumeKey false reply).1).encode (consumeKey false reply).2) >>= _) = _
      rw [request_tree (consumeKey false reply), vis_bind]
    | change (sig.primitive (consumeKey true reply).1
        ((sig.argument (consumeKey true reply).1).encode (consumeKey true reply).2) >>= _) = _
      rw [request_tree (consumeKey true reply), vis_bind]
    simp [splitTransfer]
    rfl

/-- Each tag evaluates the payload producer once, then exposes its tagged
reply at the consumer and returns through the corresponding ordered exit. -/
theorem packed_tags (left : Bool) :
    built.observe sig.primitive (fun _ => .unit) (NamedFlat.Capture.packEnv 2 (env left)) =
      expected left := by
  rw [built.packed_run, source_run]

example (payload : Denote bit) : consumeKey true payload ≠ consumeKey false payload := by
  intro same
  have tags : (Sum.inl payload : Denote choice) = Sum.inr payload :=
    eq_of_heq (Sigma.mk.inj_iff.mp same).2
  cases tags

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.InjectionOperandExamples
