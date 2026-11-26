module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.Elgot.ITree (HasTrace TraceLE Trace hasTrace_vis_exchange_iff
  out out_injective out_vis out_ret vis ret vis_bind)
open Silmaril.Elgot.ITree.Finite (evaluate headFrom out_evaluate)
open PacketType (encode)

private inductive Opcode
  | poll
  | ping
  deriving DecidableEq

private def bit : PacketType := .coprod .unit .unit
private def three : PacketType := .coprod .unit bit

private def sig : PrimitiveSignature Opcode :=
  ⟨fun | .poll => bit | .ping => .unit, three⟩

private def inputType : PacketType := .product bit .unit
private def replyType : PacketType := .product three bit
private def inputs : Fin 1 → PacketType := fun _ => inputType
private def outputs : Fin 2 → PacketType := Fin.cases .unit (fun _ => bit)
private def localType : Fin 2 → PacketType := Fin.cases inputType (fun _ => replyType)
private def types : Label 2 2 → PacketType := Sum.elim localType outputs

private def entryCode : Code sig types [inputType] :=
  .unpack (.var .here)
    (.apply .poll (.var (.there .here)) (.inl 1) (.pair (.var .here) (.var (.there (.there .here)))))

-- The left reply takes a backedge with the retained Boolean packet.
-- The two right replies leave through different typed public ports.
private def replyCode (thirdExitsRight : Bool) : Code sig types [replyType] :=
  .unpack (.var .here) (.term (.case (.var (.there .here))
    (.jump (.inl 0) (.pair (.var (.there .here)) .unit))
    (.case (.var .here)
      (.jump (.inr 0) .unit)
      (if thirdExitsRight then .jump (.inr 1) (.var (.there (.there .here))) else .jump (.inr 0) .unit))))

private def program (thirdExitsRight : Bool) : Program sig inputs outputs where
  locals := 2
  localType := localType
  entry _ := .inl 0
  entryType _ := rfl
  block i := Fin.cases entryCode (fun _ => replyCode thirdExitsRight) i

private abbrev left := program true
private abbrev right := program false

private def flag : Denote bit := .inr ⟨⟩
private def packet : Denote (inputs 0) := (flag, ⟨⟩)
private def loopReply : sig.Reply := .inl ⟨⟩
private def middleReply : sig.Reply := .inr (.inl ⟨⟩)
private def lastReply : sig.Reply := .inr (.inr ⟨⟩)
private def key : sig.Request := ⟨.poll, flag⟩


private def leftReply (reply : sig.Reply) : left.State :=
  ⟨⟨.inl ⟨1, by decide⟩, (reply, flag)⟩⟩

private def rightReply (reply : sig.Reply) : right.State :=
  ⟨⟨.inl ⟨1, by decide⟩, (reply, flag)⟩⟩

private theorem leftStart : headFrom left.step left.states (left.start 0 packet) = .request key leftReply := by cbv
private theorem leftLoop : headFrom left.step left.states (leftReply loopReply) = .request key leftReply := by cbv
private theorem rightStart : headFrom right.step right.states (right.start 0 packet) = .request key rightReply := by cbv
private theorem rightLoop : headFrom right.step right.states (rightReply loopReply) = .request key rightReply := by cbv

private def exitFirst : Program.Result outputs := ⟨⟨0, ⟨⟩⟩⟩
private def exitSecond : Program.Result outputs := ⟨⟨1, flag⟩⟩

example : headFrom left.step left.states (leftReply middleReply) = .result exitFirst := by cbv
private theorem leftLast : headFrom left.step left.states (leftReply lastReply) = .result exitSecond := by cbv
private theorem rightLast : headFrom right.step right.states (rightReply lastReply) = .result exitFirst := by cbv

private theorem seesRequest (p : Program sig inputs outputs) (s : p.State) (next : sig.Reply → p.State)
    (found : headFrom p.step p.states s = .request key next) :
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
  .exchange (.ask key) loopReply
    (.exchange (.ask key) lastReply (.result (Program.renderResult exitSecond)))

private theorem leftTrace : HasTrace (left.observe 0 packet) trace := by
  unfold trace
  rw [Program.observe_eq, seesRequest left _ _ leftStart, vis_bind, hasTrace_vis_exchange_iff]
  change HasTrace (evaluate left.step (leftReply loopReply) >>= _) _
  rw [seesRequest left _ _ leftLoop, vis_bind, hasTrace_vis_exchange_iff]
  change HasTrace (evaluate left.step (leftReply lastReply) >>= _) _
  rw [seesResult left _ _ leftLast]
  exact out_ret _

private theorem missingRightTrace : ¬ HasTrace (right.observe 0 packet) trace := by
  unfold trace
  rw [Program.observe_eq, seesRequest right _ _ rightStart, vis_bind, hasTrace_vis_exchange_iff]
  change ¬ HasTrace (evaluate right.step (rightReply loopReply) >>= _) _
  rw [seesRequest right _ _ rightLoop, vis_bind, hasTrace_vis_exchange_iff]
  change ¬ HasTrace (evaluate right.step (rightReply lastReply) >>= _) _
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
