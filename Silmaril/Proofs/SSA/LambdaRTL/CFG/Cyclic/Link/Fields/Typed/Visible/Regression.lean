module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Reindex.Thms
import Mathlib.Tactic.FinCases
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Defs

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.Elgot.ITree (HasTrace TraceLE Trace hasTrace_vis_exchange_iff
  out out_injective out_vis out_ret vis ret vis_bind)
open Silmaril.Elgot.ITree.Finite (compare compareUnder evaluate headFrom out_evaluate)

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

-- A handler that denies every reply cannot replay this distinguishing
-- exchange path, even though it is present in the unrestricted weak tree.
private def denyReplies : Silmaril.Logic.ITree.Model.{0, 0} sig.traceSignature.toSignature where
  State := Unit
  initial _ := True
  step _ _ _ _ := False

example : ¬ Silmaril.Elgot.ITree.Replay denyReplies.step () trace := by
  simp [trace, Silmaril.Elgot.ITree.Replay, denyReplies]

-- Keep the looping and middle poll replies and all ping replies.
-- Only the reply that reaches the distinguishing exit is denied.
private def admitCommon (key : sig.Request) (reply : sig.Reply key) : Bool :=
  match key with
  | ⟨.ping, _⟩ => true
  | ⟨.poll, _⟩ =>
    match reply with
    | .inr (.inr _) => false
    | _ => true

example : ¬ Silmaril.Elgot.ITree.Replay (sig.traceModelUnder admitCommon).step () trace := by
  simp [trace, Silmaril.Elgot.ITree.Replay, PrimitiveSignature.traceModelUnder,
    Silmaril.Elgot.ITree.Finite.replyHandler, admitCommon, pollKey, pingKey, lastReply]

private def admittedPrefix : Program.ObservationTrace sig :=
  .exchange (.ask pollKey) loopReply (.exchange (.ask pingKey) pingReply (.request (.ask pollKey)))

example : Silmaril.Elgot.ITree.Replay (sig.traceModelUnder admitCommon).step () admittedPrefix := by
  exact ⟨(), rfl, (), rfl, trivial⟩

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

-- Even a handler denying every reply can observe a different pending key.
#guard !(compareUnder (fun _ _ => false) left.states left.states left.step left.step
  (left.start 0 packet) (left.start 0 (.inl ⟨⟩, ⟨⟩)))

-- Starting at ping places the distinguishing poll reply behind a matching
-- exchange. The extracted path has both opcodes and the ordered return.
private def viaPing (thirdExitsRight : Bool) : Program sig (fun _ : Fin 1 => bit) outputs where
  locals := 3
  localType := localType
  entry _ := .inl 2
  entryType _ := rfl
  block := (program thirdExitsRight).block

#guard
  match (viaPing true).explainMismatch? (viaPing false) with
  | some ⟨_, .leftToRight, .exchange (.ask ⟨.ping, _⟩) _
      (.exchange (.ask ⟨.poll, _⟩) reply (.result (1, _)))⟩ =>
    match PacketType.encode three reply with
    | .inr (.inr .unit) => true
    | _ => false
  | _ => false

-- Completing ping changes admission of the exact same poll key and reply.
-- The loop and middle replies remain available in both handler states.
private def advance (closed : Bool) (key : sig.Request) (reply : sig.Reply key) : Option Bool :=
  match key with
  | ⟨.ping, _⟩ => some true
  | ⟨.poll, _⟩ =>
    match reply with
    | .inr (.inr _) => if closed then none else some false
    | _ => some closed

private def startOpen (closed : Bool) : Bool := !closed
private abbrev protocol := sig.traceModelWithHandler advance startOpen

private def lastExchange : Program.ObservationTrace sig :=
  .exchange (.ask pollKey) lastReply (.result (Program.renderResult exitSecond))

example : Silmaril.Elgot.ITree.Replay protocol.step false lastExchange :=
  ⟨false, rfl, trivial⟩

example : ¬ Silmaril.Elgot.ITree.Replay protocol.step true lastExchange := by
  rintro ⟨_, impossible, _⟩
  cases impossible

example : ¬ Silmaril.Elgot.ITree.Replay protocol.step false trace := by
  rintro ⟨first, hfirst, second, hsecond, _, impossible, _⟩
  change some false = some first at hfirst
  change some true = some second at hsecond
  cases hfirst
  cases hsecond
  cases impossible

example : Silmaril.Elgot.ITree.Replay protocol.step false admittedPrefix :=
  ⟨false, rfl, true, rfl, trivial⟩

#guard !(left.refinementAtWithHandler? advance right 0 packet false)
#guard left.refinementAtWithHandler? advance right 0 packet true
#guard (viaPing true).refinementWithHandler? advance startOpen (viaPing false) 0 flag

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

private def packedLeft : Program.PackedEntry left 0 :=
  ⟨1, captures, captureTypes, localType, outputs, leftTarget, rfl, leftTyped⟩

private def packedRight : Program.PackedEntry right 0 :=
  ⟨1, captures, captureTypes, localType, outputs, rightTarget, rfl, rightTyped⟩

private noncomputable def sentence :=
  packedLeft.refinementSentence packedRight .leftToRight ambient ambient env env

example : ¬ Silmaril.Logic.ITree.TraceInstitution.institution.{0, 1, 0}.Sat sig.traceSignature
    ⟨sig.traceModel⟩ sentence := by
  intro sat
  have pass := (Program.refinementAt?_iff_traceSat packet packedLeft packedRight
    ambient ambient env env (fun _ => rfl) (fun _ => rfl)).mpr sat
  simp [rejected] at pass

example : Silmaril.Logic.ITree.TraceInstitution.institution.{0, 1, 0}.Sat sig.traceSignature
    ⟨sig.traceModelUnder admitCommon⟩ sentence :=
  (Program.refinementAtUnder?_iff_traceSat admitCommon packet packedLeft packedRight
    ambient ambient env env (fun _ => rfl) (fun _ => rfl)).mp (by cbv)

-- The restrictive handler satisfies this particular sentence, but the
-- unrestricted policy still witnesses failure of shared-handler validity.
example : ¬ (∀ policy : Silmaril.Logic.ITree.Model.{0, 0} sig.traceSignature.toSignature,
    Silmaril.Logic.ITree.TraceInstitution.Sat policy sentence) := by
  intro valid
  have accepted := (Program.refinementAt?_iff_valid_traceSat packet packedLeft packedRight
    ambient ambient env env (fun _ => rfl) (fun _ => rfl)).mpr valid
  simp [rejected] at accepted

-- A smaller checked dispatcher exercises the state update and the
-- ordered-exit distinction with a kernel-reducible product.
private def unitSig : PrimitiveSignature Opcode :=
  ⟨fun _ => .unit, fun _ => .unit⟩

private def unitInputs : Fin 1 → PacketType := fun _ => .unit
private def unitPorts : Fin 2 → PacketType := fun _ => .unit

private def gatedExit (port : Fin 2) : Program unitSig unitInputs unitPorts where
  locals := 2
  localType := unitPorts
  entry _ := .inl 0
  entryType _ := rfl
  block i := Fin.cases (.apply .ping .unit (.inl 1) .unit)
    (fun _ => .apply .poll .unit (.inr port) .unit) i

private def gate (closed : Bool) (key : unitSig.Request) (_ : unitSig.Reply key) : Option Bool :=
  match key.1 with
  | .ping => some true
  | .poll => if closed then none else some false

private def unitContext : BoundCtx PacketType 1 := .snoc .nil .unit

private theorem gatedAdmitted (port : Fin 2) :
    (elaborate ((gatedExit port).compile 0) (gatedExit port).exits captures).isSome := by
  fin_cases port <;> decide

private def gatedTarget (port : Fin 2) :=
  (elaborate ((gatedExit port).compile 0) (gatedExit port).exits captures).get (gatedAdmitted port)

private def packedGated (port : Fin 2) : Program.PackedEntry (gatedExit port) 0 where
  count := 1
  captures := captures
  context := unitContext
  blocks := unitPorts
  exits := unitPorts
  target := gatedTarget port
  accepted := Option.eq_some_of_isSome (gatedAdmitted port)
  typed := by
    let _ := unitSig.typing
    exact check_sound _ _ _ _ (by fin_cases port <;> decide)

private def unitPacket : Denote (unitInputs 0) := ⟨⟩

private noncomputable def gatedSentence :=
  (packedGated 0).refinementSentence (packedGated 1) .leftToRight ambient ambient ambient ambient

example : Silmaril.Logic.ITree.TraceInstitution.institution.{0, 1, 0}.Sat unitSig.traceSignature
    ⟨unitSig.traceModelWithHandler gate startOpen⟩ gatedSentence :=
  (Program.refinementWithHandler?_iff_traceSat gate startOpen unitPacket (packedGated 0) (packedGated 1)
    ambient ambient ambient ambient (fun _ => rfl) (fun _ => rfl)).mp (by cbv)

example : ¬ Silmaril.Logic.ITree.TraceInstitution.institution.{0, 1, 0}.Sat unitSig.traceSignature
    ⟨unitSig.traceModelWithHandler (fun h _ _ => some h) startOpen⟩ gatedSentence := by
  intro sat
  have accepted := (Program.refinementWithHandler?_iff_traceSat (fun h _ _ => some h) startOpen unitPacket
    (packedGated 0) (packedGated 1) ambient ambient ambient ambient (fun _ => rfl) (fun _ => rfl)).mpr sat
  have rejected : (gatedExit 0).refinementWithHandler? (fun h _ _ => some h) startOpen (gatedExit 1) 0 unitPacket = false := by cbv
  simp [rejected] at accepted

section EventRename

open CategoryTheory
open Silmaril.Elgot.ITree (Request TraceSignature hasTrace_bind_pure_map_iff)
open Silmaril.Logic.ITree

-- The target has a fresh request and wraps each original typed reply.
private inductive Imported : Type → Type
  | wrapped (key : sig.Request) : Imported (ULift.{0} (sig.Reply key))
  | extra : Imported PUnit

private def imported : TraceSignature := ⟨⟨Imported⟩⟩

private def requestMap : Request sig.traceSignature.toSignature.Event → Request imported.toSignature.Event
  | ⟨_, .ask key⟩ => ⟨_, Imported.wrapped key⟩

private def recoverKey : Request imported.toSignature.Event → Option sig.Request
  | ⟨_, .wrapped key⟩ => some key
  | ⟨_, .extra⟩ => none

private def renameEvents : sig.traceSignature ⟶ imported where
  hom :=
    { request := requestMap
      reply := fun
        | ⟨_, .ask _⟩, reply => reply.down }
  request_injective := by
    rintro ⟨_, left⟩ ⟨_, right⟩ equal
    cases left
    cases right
    have keys := Option.some.inj (congrArg recoverKey equal)
    cases keys
    rfl
  reply_bijective := by
    rintro ⟨_, event⟩
    cases event
    exact Equiv.ulift.bijective

example (policy : Silmaril.Logic.ITree.Model.{0, 0} imported.toSignature) :
    TraceInstitution.Sat policy
      (packedLeft.refinementSentenceReindexed packedRight renameEvents .leftToRight ambient ambient env env) ↔
    TraceInstitution.Sat (policy.reduct renameEvents.hom)
      (packedLeft.refinementSentence packedRight .leftToRight ambient ambient env env) :=
  packedLeft.sat_reindexed_iff packedRight renameEvents policy .leftToRight ambient ambient env env

private def taggedTrace := trace.map FiniteCFG.packedTreeOutput
private noncomputable def importedTrace := renameEvents.trace taggedTrace

example :
    HasTrace (packedLeft.observeReindexed renameEvents ambient env) importedTrace ∧
      ¬ HasTrace (packedRight.observeReindexed renameEvents ambient env) importedTrace := by
  have namedL := packedLeft.observe_eq packet ambient env (fun _ => rfl)
  have namedR := packedRight.observe_eq packet ambient env (fun _ => rfl)
  have reflectTag := hasTrace_bind_pure_map_iff (f := FiniteCFG.packedTreeOutput)
    Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program.packedTreeOutput_injective
    (left.observe 0 packet) trace
  rw [packedLeft.observe_reindexed, packedRight.observe_reindexed]
  constructor
  · exact (renameEvents.hasTrace_image _ _).mpr
      ⟨taggedTrace, namedL.symm ▸ reflectTag.mpr leftTrace, rfl⟩
  · intro seen
    obtain ⟨pre, witnessed, same⟩ := (renameEvents.hasTrace_image _ _).mp seen
    have tag := renameEvents.trace_injective same
    subst pre
    rw [namedR] at witnessed
    apply missingRightTrace
    exact (hasTrace_bind_pure_map_iff
      Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program.packedTreeOutput_injective
      (right.observe 0 packet) trace).mp witnessed

end EventRename

end Packed

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
