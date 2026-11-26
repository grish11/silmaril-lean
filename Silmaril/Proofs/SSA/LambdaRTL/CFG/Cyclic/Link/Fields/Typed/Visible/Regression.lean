module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.Elgot.ITree (HasTrace TraceLE Trace hasTrace_vis_exchange_iff
  out out_injective out_vis out_ret vis ret vis_bind)
open Silmaril.Elgot.ITree.Finite (compare evaluate headFrom out_evaluate)
open PacketType (encode)

private inductive Opcode
  | poll
  | ping
  deriving DecidableEq

private def bit : PacketType := .coprod .unit .unit
private def three : PacketType := .coprod .unit bit

private def sig : PrimitiveSignature Opcode :=
  ⟨fun | .poll => bit | .ping => .unit, fun | .poll => three | .ping => .unit⟩

private def inputType : PacketType := .product bit .unit
private def replyType : PacketType := .product three bit
private def inputs : Fin 1 → PacketType := fun _ => inputType
private def outputs : Fin 2 → PacketType := Fin.cases .unit (fun _ => bit)
private def localType : Fin 3 → PacketType := Fin.cases inputType (Fin.cases replyType (fun _ => bit))
private def types : Label 3 2 → PacketType := Sum.elim localType outputs

private def entryCode : Code sig types [inputType] :=
  .unpack (.var .here)
    (.apply .poll (.var (.there .here)) (.inl 1) (.pair (.var .here) (.var (.there (.there .here)))))

-- The first poll reply routes the retained flag through ping before polling
-- again. The other poll replies select differently typed public ports.
private def replyCode (thirdExitsRight : Bool) : Code sig types [replyType] :=
  .unpack (.var .here) (.term (.case (.var (.there .here))
    (.jump (.inl 2) (.var (.there .here)))
    (.case (.var .here)
      (.jump (.inr 0) .unit)
      (if thirdExitsRight then .jump (.inr 1) (.var (.there (.there .here))) else .jump (.inr 0) .unit))))

private def pingCode : Code sig types [bit] :=
  .apply .ping .unit (.inl 0) (.pair (.var (.there .here)) (.var .here))

private def program (thirdExitsRight : Bool) : Program sig inputs outputs where
  locals := 3
  localType := localType
  entry _ := .inl 0
  entryType _ := rfl
  block i := Fin.cases entryCode (Fin.cases (replyCode thirdExitsRight) (fun _ => pingCode)) i

private abbrev left := program true
private abbrev right := program false

private def flag : Denote bit := .inr ⟨⟩
private def packet : Denote (inputs 0) := (flag, ⟨⟩)
private def pollKey : sig.Request := ⟨.poll, flag⟩
private def pingKey : sig.Request := ⟨.ping, ⟨⟩⟩
private def loopReply : sig.Reply pollKey := .inl ⟨⟩
private def middleReply : sig.Reply pollKey := .inr (.inl ⟨⟩)
private def lastReply : sig.Reply pollKey := .inr (.inr ⟨⟩)
private def pingReply : sig.Reply pingKey := ⟨⟩

private def pollNext (p : Bool) (reply : sig.Reply pollKey) : (program p).State := by
  change ULift (PacketAt types)
  exact ⟨⟨.inl 1, (reply, flag)⟩⟩

private def pingNext (p : Bool) (reply : sig.Reply pingKey) : (program p).State := by
  change ULift (PacketAt types)
  exact ⟨⟨.inl 0, (flag, reply)⟩⟩

private theorem leftStart : headFrom left.step left.states (left.start 0 packet) = .request pollKey (pollNext true) := by cbv
private theorem rightStart : headFrom right.step right.states (right.start 0 packet) = .request pollKey (pollNext false) := by cbv
private theorem leftPing : headFrom left.step left.states (pollNext true loopReply) = .request pingKey (pingNext true) := by cbv
private theorem rightPing : headFrom right.step right.states (pollNext false loopReply) = .request pingKey (pingNext false) := by cbv

private def exitFirst : Program.Result outputs := ⟨⟨0, ⟨⟩⟩⟩
private def exitSecond : Program.Result outputs := ⟨⟨1, flag⟩⟩

example : headFrom left.step left.states (pollNext true middleReply) = .result exitFirst := by cbv
private theorem leftLast : headFrom left.step left.states (pollNext true lastReply) = .result exitSecond := by cbv
private theorem rightLast : headFrom right.step right.states (pollNext false lastReply) = .result exitFirst := by cbv

private theorem seesRequest (p : Program sig inputs outputs) (s : p.State) (key : sig.Request)
    (next : sig.Reply key → p.State) (found : headFrom p.step p.states s = .request key next) :
    evaluate p.step s = vis (.ask key) (evaluate p.step ∘ next) := by
  apply out_injective
  rw [out_evaluate _ _ p.mem_states, found, out_vis]
  rfl

private theorem seesResult (p : Program sig inputs outputs) (s : p.State) (r : Program.Result outputs)
    (found : headFrom p.step p.states s = .result r) :
    (evaluate p.step s >>= fun r => pure (Program.renderResult r)) = ret (Program.renderResult r) := by
  have equal : evaluate p.step s = ret r := by
    apply out_injective
    rw [out_evaluate _ _ p.mem_states, found, out_ret]
    rfl
  rw [equal]
  exact pure_bind _ _

/-- Observe one complete cycle, then the third reply and the Boolean exit. -/
private def trace : Trace (Silmaril.Elgot.ITree.Finite.Event sig.Request sig.Reply)
    (Nat × Silmaril.Isotope.Value Atom) :=
  .exchange (.ask pollKey) loopReply
    (.exchange (.ask pingKey) pingReply
      (.exchange (.ask pollKey) lastReply (.result (Program.renderResult exitSecond))))

private theorem leftTrace : HasTrace (left.observe 0 packet) trace := by
  unfold trace
  rw [Program.observe_eq, seesRequest left _ _ _ leftStart, vis_bind, hasTrace_vis_exchange_iff]
  change HasTrace (evaluate left.step (pollNext true loopReply) >>= _) _
  rw [seesRequest left _ _ _ leftPing, vis_bind, hasTrace_vis_exchange_iff]
  change HasTrace (evaluate left.step (left.start 0 packet) >>= _) _
  rw [seesRequest left _ _ _ leftStart, vis_bind, hasTrace_vis_exchange_iff]
  change HasTrace (evaluate left.step (pollNext true lastReply) >>= _) _
  rw [seesResult left _ _ leftLast]
  exact out_ret _

private theorem missingRightTrace : ¬ HasTrace (right.observe 0 packet) trace := by
  unfold trace
  rw [Program.observe_eq, seesRequest right _ _ _ rightStart, vis_bind, hasTrace_vis_exchange_iff]
  change ¬ HasTrace (evaluate right.step (pollNext false loopReply) >>= _) _
  rw [seesRequest right _ _ _ rightPing, vis_bind, hasTrace_vis_exchange_iff]
  change ¬ HasTrace (evaluate right.step (right.start 0 packet) >>= _) _
  rw [seesRequest right _ _ _ rightStart, vis_bind, hasTrace_vis_exchange_iff]
  change ¬ HasTrace (evaluate right.step (pollNext false lastReply) >>= _) _
  rw [seesResult right _ _ rightLast]
  simp [HasTrace, Program.renderResult, exitFirst, exitSecond]

example : ¬ TraceLE (left.observe 0 packet) (right.observe 0 packet) :=
  fun included => missingRightTrace (included _ leftTrace)

private theorem rejected : left.refinementAt? right 0 packet = false := by
  cases decision : left.refinementAt? right 0 packet with
  | false => rfl
  | true =>
    have included := (left.refinementAt?_iff right 0 packet).mp decision
    exact (missingRightTrace (included _ leftTrace)).elim

#guard !(left.refinementAt? right 0 packet)
#guard left.refinement? left

-- Even two requests for poll differ when their typed arguments differ.
#guard !(compare left.states left.states left.step left.step
  (left.start 0 packet) (left.start 0 (.inl ⟨⟩, ⟨⟩)))

section Packed

open Silmaril (HasTy)
open Silmaril.Isotope (BoundCtx)
open Silmaril.Isotope.Bridge.NamedFlat (elaborate check_sound)
open Silmaril.Isotope.Bridge.NamedFlat.Capture (packEnv)
open Silmaril.Isotope.LambdaSSA (FiniteCFG)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (region)

private def captureTypes : BoundCtx PacketType 1 := .snoc .nil inputType
private def captures : Fin 1 → Register := fun _ => ⟨0⟩

private instance : HasTy Opcode PacketType := sig.typing

private def leftTarget := (elaborate (left.compile 0) left.exits captures).get (by decide)
private def rightTarget := (elaborate (right.compile 0) right.exits captures).get (by decide)

private theorem leftTyped : leftTarget.HasType captureTypes localType outputs :=
  check_sound leftTarget captureTypes localType outputs (by decide)

private theorem rightTyped : rightTarget.HasType captureTypes localType outputs :=
  check_sound rightTarget captureTypes localType outputs (by decide)

private def env : Silmaril.Isotope.LambdaSSA.Semantics.Env Atom := fun _ => PacketType.encode (inputs 0) packet
private def ambient : Silmaril.Isotope.LambdaSSA.Semantics.Env Atom := fun _ => .unit

example : ¬ TraceLE
    (region sig.primitive (Silmaril.Isotope.LambdaSSA.Semantics.extend ambient (packEnv 1 env))
      ((FiniteCFG.packedExecutionRegion leftTyped).packInputsDestructure captureTypes.toList))
    (region sig.primitive (Silmaril.Isotope.LambdaSSA.Semantics.extend ambient (packEnv 1 env))
      ((FiniteCFG.packedExecutionRegion rightTyped).packInputsDestructure captureTypes.toList)) := by
  intro included
  have l := left.packed_observe 0 packet captures rfl leftTyped ambient env (fun _ => rfl)
  have r := right.packed_observe 0 packet captures rfl rightTyped ambient env (fun _ => rfl)
  have included' := congrArg₂ TraceLE l r ▸ included
  have accepted := (left.refinementAt?_iff_packedOutput right 0 packet).mpr included'
  simp [rejected] at accepted

end Packed

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
