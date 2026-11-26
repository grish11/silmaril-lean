module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.CaseExamples

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Transfer region)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (Atom Denote PacketType PrimitiveSignature Program)
open Silmaril.Elgot.ITree (Tree Trace HasTrace ret vis iterate_fixpoint vis_bind hasTrace_vis_exchange_iff out_ret)
open Silmaril.Elgot.ITree.Finite (Event evaluate transition)

private def bit : PacketType := .coprod .unit .unit
private def replyType : PacketType := .coprod bit bit
private def sig : PrimitiveSignature Bool :=
  ⟨fun poll => if poll then .product bit bit else bit, fun poll => if poll then replyType else bit⟩
private abbrev Events := Event sig.Request sig.Reply

private def packets (_ : Fin 1) : PacketType := bit
private def exits (i : Fin 2) : PacketType := if i.val = 0 then .unit else .product bit bit

-- The second reply makes the selected row either revisit itself with
-- a new argument, or return the case payload paired with this visit's input.
private def polling : FiniteCFG Bool 1 2 1 where
  entry := .br 0 (.bv 0)
  block _ := .let₁ (.op false (.bv 0)) (.let₁ (.op true (.pair (.bv 1) (.bv 0)))
    (.case (.bv 0) (.br 0 (.bv 0)) (.br 2 (.pair (.bv 0) (.bv 3)))))

private def checked : Checked sig (.snoc .nil bit) packets exits polling :=
  (check sig (.snoc .nil bit) packets exits polling).get (by decide)

private def built :=
  (construct sig (fun i => (checked.shape.table i).1) exits checked.emitted.code).get (by decide)

example : checked.shape.row.requests = 2 := rfl
example : (checked.emitted.code.block 2).erase =
    .let₂ (.var 0) (.let₂ (.var 1)
      (.case (.var 2) (.br 0 (.var 0)) (.br 4 (.pair (.var 0) (.var 2))))) := rfl

-- A request inside a case leaf still falls outside the literal jump grammar.
example : (readRow sig packets exits [replyType] (.case (.var 0)
    (.let₁ (.op false (.var 0)) (.br 0 (.var 0))) (.br 2 (.pair (.var 0) (.var 0))))).isNone = true := rfl

private def dispatcher := built.program

private def primeKey (input : Denote bit) : sig.Request := ⟨false, input⟩
private def pollKey (input prime : Denote bit) : sig.Request := ⟨true, (input, prime)⟩

private def afterPrime (input prime : Denote bit) : dispatcher.State := by
  refine ⟨⟨.inl ⟨1, by decide⟩, ?_⟩⟩
  change Denote bit × Denote bit
  exact (input, prime)

private def afterPoll (input prime : Denote bit) (reply : Denote replyType) : dispatcher.State := by
  refine ⟨⟨.inl ⟨2, by decide⟩, ?_⟩⟩
  change (Denote bit × Denote bit) × Denote replyType
  exact ((input, prime), reply)

private def returned (payload input : Denote bit) : dispatcher.State := ⟨⟨.inr 1, (payload, input)⟩⟩

private theorem prime_step (input : Denote bit) :
    dispatcher.step (dispatcher.start 0 input) = .inl (.request (primeKey input) (afterPrime input)) := rfl

private theorem poll_step (input prime : Denote bit) :
    dispatcher.step (afterPrime input prime) = .inl (.request (pollKey input prime) (afterPoll input prime)) := rfl

private theorem repeat_step (input prime next : Denote bit) :
    dispatcher.step (afterPoll input prime (.inl next)) = .inr (dispatcher.start 0 next) := rfl

private theorem exit_step (input prime payload : Denote bit) :
    dispatcher.step (afterPoll input prime (.inr payload)) = .inr (returned payload input) := rfl

private theorem ret_eq_pure {A : Type 1} (value : A) : ret (E := Events) value = pure value := rfl

section Execution

variable {inputs : Fin 1 → PacketType} (program : Program sig inputs exits)

private noncomputable def runState (state : program.State) : Tree Events (Transfer Atom) :=
  evaluate program.step state >>= fun r => pure (FiniteCFG.packedTreeOutput (Program.renderResult r))

private theorem run_request {state : program.State} (key : sig.Request)
    (resume : sig.Reply key → program.State) (step : program.step state = .inl (.request key resume)) :
    runState program state = vis (.ask key) (fun reply => runState program (resume reply)) := by
  unfold runState evaluate
  rw [congrFun (iterate_fixpoint (transition program.step)) state]
  simp only [transition, step, vis_bind, ret_eq_pure, pure_bind, Sum.elim_inr]

private theorem run_jump {here next : program.State} (step : program.step here = .inr next) :
    runState program here = runState program next := by
  unfold runState evaluate
  rw [congrFun (iterate_fixpoint (transition program.step)) here]
  simp only [transition, step, ret_eq_pure, pure_bind, Sum.elim_inr]

private theorem run_result {state : program.State} {result : Program.Result exits}
    (step : program.step state = .inl (.result result)) :
    runState program state = pure (FiniteCFG.packedTreeOutput (Program.renderResult result)) := by
  unfold runState evaluate
  rw [congrFun (iterate_fixpoint (transition program.step)) state]
  simp only [transition, step, ret_eq_pure, pure_bind, Sum.elim_inl]

end Execution

private def output (payload input : Denote bit) : Transfer Atom :=
  FiniteCFG.packedTreeOutput (1, .pair (bit.encode payload) (bit.encode input))

private theorem run_exit (payload input : Denote bit) :
    runState dispatcher (returned payload input) = pure (output payload input) :=
  run_result dispatcher (result := ⟨⟨1, (payload, input)⟩⟩) rfl

private def env (input : Denote bit) : Env Atom := fun _ => bit.encode input

private theorem codec_id (value : Value Atom) : valueCodec id value = value := by
  induction value <;> simp_all only [valueCodec, id_eq]

private theorem primitivesAgree : PrimitivesAgree sig.primitive sig.primitive id := by
  intro op value
  rw [codec_id, show valueCodec (id : Atom → Atom) = id from funext codec_id, id_map]

private noncomputable def original {blocks : Nat} (graph : FiniteCFG Bool blocks 2 1)
    (input : Denote bit) : Tree Events (Transfer Atom) :=
  resultCodec id <$> (region sig.primitive (env input) graph.erase >>=
    fun out => pure (FiniteCFG.packedTreeOutput out))

private theorem source_packed (input : Denote bit) :
    original polling input = built.packed.observe (env input) (env input) :=
  checked.emitted.public_run built (env input) (env input) (env input) id primitivesAgree (codec_id _).symm

private theorem packed_state (input : Denote bit) :
    built.packed.observe (env input) (env input) = runState dispatcher (dispatcher.start 0 input) := by
  rw [built.packed.observe_eq input _ _ (fun _ => rfl)]
  change (dispatcher.observe 0 input >>= fun out => pure (FiniteCFG.packedTreeOutput out)) = _
  rw [dispatcher.observe_eq 0 input]
  simp only [runState, bind_assoc, pure_bind]

private def first : Denote bit := .inl ⟨⟩
private def second : Denote bit := .inr ⟨⟩

private def repeatThenExit : Trace Events (Transfer Atom) :=
  .exchange (.ask (primeKey first)) second
    (.exchange (.ask (pollKey first second)) (.inl second)
      (.exchange (.ask (primeKey second)) first
        (.exchange (.ask (pollKey second first)) (.inr first) (.result (output first second)))))

/-- Each visit completes both requests. The final reply selects the exit
and its payload survives alongside the second visit's input. -/
theorem repeat_then_exit :
    HasTrace (original polling first) repeatThenExit ∧
      HasTrace (built.packed.observe (env first) (env first)) repeatThenExit := by
  have trace : HasTrace (runState dispatcher (dispatcher.start 0 first)) repeatThenExit := by
    unfold repeatThenExit
    rw [run_request dispatcher _ _ (prime_step first)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_request dispatcher _ _ (poll_step first second)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump dispatcher (repeat_step first second second), run_request dispatcher _ _ (prime_step second)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_request dispatcher _ _ (poll_step second first)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump dispatcher (exit_step second first first), run_exit]
    exact out_ret _
  rw [source_packed, packed_state]
  exact ⟨trace, trace⟩

-- Both leaves stay within the old table. Block one receives only the
-- case payload and feeds it back. Block two receives the case payload
-- and the pre-request input, then returns that pair on the second exit.
private def internalPackets (i : Fin 3) : PacketType :=
  if i.val = 2 then .product bit bit else bit

private def internalPolling : FiniteCFG Bool 3 2 1 where
  entry := .br 0 (.bv 0)
  block i :=
    if i.val = 0 then .let₁ (.op true (.pair (.bv 0) (.bv 0)))
      (.case (.bv 0) (.br 1 (.bv 0)) (.br 2 (.pair (.bv 0) (.bv 2))))
    else if i.val = 1 then .br 0 (.bv 0)
    else .br 4 (.bv 0)

private def internalChecked : Checked sig (.snoc .nil bit) internalPackets exits internalPolling :=
  (check sig (.snoc .nil bit) internalPackets exits internalPolling).get (by decide)

private def internalBuilt :=
  (construct sig (fun i => (internalChecked.shape.table i).1) exits internalChecked.emitted.code).get (by decide)

private def internalDispatcher := internalBuilt.program

example : (internalBuilt.packed.target.block ((3 : Fin 4).cast internalBuilt.provenance.count)).erase =
    .let₂ (.var 0) (.case (.var 0) (.br 1 (.var 0)) (.br 2 (.pair (.var 0) (.var 2)))) :=
  (Constructed.row_erasure sig _ exits internalBuilt 3).symm.trans rfl

private def internalTail (input : Denote bit) (reply : Denote replyType) : internalDispatcher.State := by
  refine ⟨⟨.inl ⟨3, by decide⟩, ?_⟩⟩
  change Denote bit × Denote replyType
  exact (input, reply)

private def feedback (payload : Denote bit) : internalDispatcher.State := by
  refine ⟨⟨.inl ⟨1, by decide⟩, ?_⟩⟩
  exact payload

private def forward (payload input : Denote bit) : internalDispatcher.State := by
  refine ⟨⟨.inl ⟨2, by decide⟩, ?_⟩⟩
  change Denote bit × Denote bit
  exact (payload, input)

private def internalReturn (payload input : Denote bit) : internalDispatcher.State :=
  ⟨⟨.inr 1, (payload, input)⟩⟩

private theorem internal_request (input : Denote bit) :
    internalDispatcher.step (internalDispatcher.start 0 input) =
      .inl (.request (pollKey input input) (internalTail input)) := rfl

private theorem internal_left (input payload : Denote bit) :
    internalDispatcher.step (internalTail input (.inl payload)) = .inr (feedback payload) := rfl

private theorem internal_right (input payload : Denote bit) :
    internalDispatcher.step (internalTail input (.inr payload)) = .inr (forward payload input) := rfl

private theorem feedback_step (payload : Denote bit) :
    internalDispatcher.step (feedback payload) = .inr (internalDispatcher.start 0 payload) := rfl

private theorem forward_step (payload input : Denote bit) :
    internalDispatcher.step (forward payload input) = .inr (internalReturn payload input) := rfl

private theorem internal_source_packed (input : Denote bit) :
    original internalPolling input = internalBuilt.packed.observe (env input) (env input) :=
  internalChecked.emitted.public_run internalBuilt (env input) (env input) (env input) id primitivesAgree
    (codec_id _).symm

private theorem internal_packed_state (input : Denote bit) :
    internalBuilt.packed.observe (env input) (env input) =
      runState internalDispatcher (internalDispatcher.start 0 input) := by
  rw [internalBuilt.packed.observe_eq input _ _ (fun _ => rfl)]
  change (internalDispatcher.observe 0 input >>= fun out => pure (FiniteCFG.packedTreeOutput out)) = _
  rw [internalDispatcher.observe_eq 0 input]
  simp only [runState, bind_assoc, pure_bind]

private def pollTwiceTrace : Trace Events (Transfer Atom) :=
  .exchange (.ask (pollKey first first)) (.inl second)
    (.exchange (.ask (pollKey second second)) (.inr first) (.result (output first second)))

/-- The two internal jumps carry different packet types. The first
causes another visit and the second carries the distinct return fields. -/
theorem two_internal_leaves :
    HasTrace (original internalPolling first) pollTwiceTrace ∧
      HasTrace (internalBuilt.packed.observe (env first) (env first)) pollTwiceTrace := by
  have trace : HasTrace (runState internalDispatcher (internalDispatcher.start 0 first)) pollTwiceTrace := by
    unfold pollTwiceTrace
    rw [run_request internalDispatcher _ _ (internal_request first)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump internalDispatcher (internal_left first second), run_jump internalDispatcher (feedback_step second),
      run_request internalDispatcher _ _ (internal_request second)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump internalDispatcher (internal_right second first), run_jump internalDispatcher (forward_step first second),
      run_result internalDispatcher (result := ⟨⟨1, (first, second)⟩⟩) rfl]
    exact out_ret _
  rw [internal_source_packed, internal_packed_state]
  exact ⟨trace, trace⟩

private def outwardPolling : FiniteCFG Bool 1 2 1 where
  entry := .br 0 (.bv 0)
  block _ := .let₁ (.op true (.pair (.bv 0) (.bv 0)))
    (.case (.bv 0) (.br 1 .unit) (.br 2 (.pair (.bv 0) (.bv 2))))

private def outwardChecked : Checked sig (.snoc .nil bit) packets exits outwardPolling :=
  (check sig (.snoc .nil bit) packets exits outwardPolling).get (by decide)

example : (construct sig (fun i => (outwardChecked.shape.table i).1) exits
    outwardChecked.emitted.code).isSome = true := by decide

-- The backedge and second exit both run through two case binders.
-- The inner test uses the outer payload on the left and the saved input
-- on the right. The outward leaf reads both values across the inner binder.
private def nestedPolling : FiniteCFG Bool 1 2 1 where
  entry := .br 0 (.bv 0)
  block _ := .let₁ (.op true (.pair (.bv 0) (.bv 0)))
    (.case (.bv 0)
      (.case (.bv 0) (.br 1 (.bv 0)) (.br 0 (.bv 1)))
      (.case (.bv 2) (.br 1 (.bv 0)) (.br 2 (.pair (.bv 1) (.bv 3)))))

private def nestedChecked : Checked sig (.snoc .nil bit) packets exits nestedPolling :=
  (check sig (.snoc .nil bit) packets exits nestedPolling).get (by decide)

private def nestedBuilt :=
  (construct sig (fun i => (nestedChecked.shape.table i).1) exits nestedChecked.emitted.code).get (by decide)

private def nestedDispatcher := nestedBuilt.program

example : (nestedBuilt.packed.target.block ((1 : Fin 2).cast nestedBuilt.provenance.count)).erase =
    .let₂ (.var 0) (.case (.var 0)
      (.case (.var 0) (.br 2 (.var 0)) (.br 0 (.var 1)))
      (.case (.var 2) (.br 2 (.var 0)) (.br 3 (.pair (.var 1) (.var 3))))) :=
  (Constructed.row_erasure sig _ exits nestedBuilt 1).symm.trans rfl

-- The innermost payload here is unit, so it cannot feed the old bit packet.
example : (readRow sig packets exits [replyType]
    (.case (.var 0) (.case (.var 0) (.br 0 (.var 0)) (.br 0 (.var 1))) (.br 1 .unit))).isNone = true := rfl

private def nestedTail (input : Denote bit) (reply : Denote replyType) : nestedDispatcher.State := by
  refine ⟨⟨.inl ⟨1, by decide⟩, ?_⟩⟩
  change Denote bit × Denote replyType
  exact (input, reply)

private def nestedReturn (payload input : Denote bit) : nestedDispatcher.State := ⟨⟨.inr 1, (payload, input)⟩⟩

private theorem nested_request (input : Denote bit) :
    nestedDispatcher.step (nestedDispatcher.start 0 input) =
      .inl (.request (pollKey input input) (nestedTail input)) := rfl

private theorem nested_repeat :
    nestedDispatcher.step (nestedTail first (.inl second)) =
      .inr (nestedDispatcher.start 0 second) := rfl

private theorem nested_exit (payload : Denote bit) :
    nestedDispatcher.step (nestedTail second (.inr payload)) = .inr (nestedReturn payload second) := rfl

private theorem nested_source_packed (input : Denote bit) :
    original nestedPolling input = nestedBuilt.packed.observe (env input) (env input) :=
  nestedChecked.emitted.public_run nestedBuilt (env input) (env input) (env input) id primitivesAgree
    (codec_id _).symm

private theorem nested_packed_state (input : Denote bit) :
    nestedBuilt.packed.observe (env input) (env input) =
      runState nestedDispatcher (nestedDispatcher.start 0 input) := by
  rw [nestedBuilt.packed.observe_eq input _ _ (fun _ => rfl)]
  change (nestedDispatcher.observe 0 input >>= fun out => pure (FiniteCFG.packedTreeOutput out)) = _
  rw [nestedDispatcher.observe_eq 0 input]
  simp only [runState, bind_assoc, pure_bind]

/-- The outer payload crosses an inner binder on the backedge and on the
exit. The second visit's retained input is also part of the exit packet. -/
theorem nested_leaves :
    HasTrace (original nestedPolling first) pollTwiceTrace ∧
      HasTrace (nestedBuilt.packed.observe (env first) (env first)) pollTwiceTrace := by
  have trace : HasTrace (runState nestedDispatcher (nestedDispatcher.start 0 first)) pollTwiceTrace := by
    unfold pollTwiceTrace
    rw [run_request nestedDispatcher _ _ (nested_request first)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump nestedDispatcher nested_repeat, run_request nestedDispatcher _ _ (nested_request second)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump nestedDispatcher (nested_exit first),
      run_result nestedDispatcher (result := ⟨⟨1, (first, second)⟩⟩) rfl]
    exact out_ret _
  rw [nested_source_packed, nested_packed_state]
  exact ⟨trace, trace⟩

-- The caller can skip the loop and return at exit 1, carrying both the
-- entry case payload and an older capture. The other arm starts the loop.
private def branchPolling : FiniteCFG Bool 1 2 2 where
  entry := .case (.bv 0) (.br 0 (.bv 0)) (.br 2 (.pair (.bv 0) (.bv 2)))
  block _ := .let₁ (.op true (.pair (.bv 0) (.bv 0)))
    (.case (.bv 0) (.br 0 (.bv 0)) (.br 1 .unit))

private def branchContext : BoundCtx PacketType 2 := .snoc (.snoc .nil bit) replyType

private def branchBuilt : BranchEntry.Compiled sig branchContext packets exits branchPolling :=
  (BranchEntry.compile sig branchContext packets exits branchPolling 0).get (by decide)

-- The ordinary type checker accepts this entry, but the public structural
-- entry checker rejects a primitive in a case leaf.
private def effectfulEntry : FiniteCFG Bool 1 2 2 where
  entry := .case (.bv 0)
    (.let₁ (.op false (.bv 0)) (.br 0 (.bv 0))) (.br 2 (.pair (.bv 0) (.bv 2)))
  block := branchPolling.block

example : letI := sig.typing; NamedFlat.check effectfulEntry branchContext packets exits = true := rfl
example : (BranchEntry.prepare sig branchContext packets exits effectfulEntry).isNone = true := rfl

private def branchPublic := branchBuilt.publicReadback
private def branchDispatcher := branchPublic.program

example : (branchPublic.packed.target.block ((1 : Fin 3).cast branchPublic.provenance.count)).erase =
    .let₂ (.var 0) (.let₂ (.var 1)
      (.case (.var 2) (.br 0 (.var 0)) (.br 4 (.pair (.var 0) (.var 1))))) :=
  (Constructed.row_erasure sig _ exits branchPublic 1).symm.trans rfl

private def branchEnv (choice : Denote replyType) (saved : Denote bit) : Env Atom
  | 0 => replyType.encode choice
  | _ => bit.encode saved

private def callerPacket (choice : Denote replyType) (saved : Denote bit) :
    Denote ((branchBuilt.split.shape.table branchPublic.start).1) := ((⟨⟩, saved), choice)

private def branchRecord (choice : Denote replyType) (saved : Denote bit) : Env Atom :=
  fun _ => NamedFlat.Capture.packEnv 2 (branchEnv choice saved)

private noncomputable def writtenBranch (choice : Denote replyType) (saved : Denote bit) :
    Tree Events (Transfer Atom) :=
  resultCodec id <$> (region sig.primitive (branchEnv choice saved) branchPolling.erase >>=
    fun out => pure (FiniteCFG.packedTreeOutput out))

private theorem branch_agreement (choice : Denote replyType) (saved : Denote bit) :
    writtenBranch choice saved = branchPublic.packed.observe (branchEnv choice saved) (branchRecord choice saved) :=
  branchBuilt.public_run (branchEnv choice saved) _ _ id primitivesAgree (codec_id _).symm

private theorem branch_packed_state (choice : Denote replyType) (saved : Denote bit) :
    branchPublic.packed.observe (branchEnv choice saved) (branchRecord choice saved) =
      runState branchDispatcher (branchDispatcher.start 0 (callerPacket choice saved)) := by
  rw [branchPublic.packed.observe_eq (callerPacket choice saved) _ _ (fun _ => rfl)]
  change (branchDispatcher.observe 0 (callerPacket choice saved) >>= fun out =>
    pure (FiniteCFG.packedTreeOutput out)) = _
  rw [branchDispatcher.observe_eq 0 (callerPacket choice saved)]
  simp only [runState, bind_assoc, pure_bind]

private def branchRow (input : Denote bit) : branchDispatcher.State := by
  refine ⟨⟨.inl ⟨0, by decide⟩, ?_⟩⟩
  change Denote bit
  exact input

private def branchResume (input : Denote bit) (reply : Denote replyType) : branchDispatcher.State := by
  refine ⟨⟨.inl ⟨2, by decide⟩, ?_⟩⟩
  change Denote bit × Denote replyType
  exact (input, reply)

/-- The bypass arm returns directly at the second ordered exit with the
case payload and older capture, with no visible requests. -/
theorem branch_bypasses_requests (payload saved : Denote bit) :
    writtenBranch (.inr payload) saved = pure (output payload saved) ∧
      branchPublic.packed.observe (branchEnv (.inr payload) saved) (branchRecord (.inr payload) saved) =
        pure (output payload saved) := by
  rw [branch_agreement (.inr payload) saved, branch_packed_state (.inr payload) saved]
  have bypass : branchDispatcher.step (branchDispatcher.start 0 (callerPacket (.inr payload) saved)) =
      .inr ⟨⟨.inr 1, (payload, saved)⟩⟩ := rfl
  rw [run_jump branchDispatcher bypass,
    run_result branchDispatcher (result := ⟨⟨1, (payload, saved)⟩⟩) rfl]
  exact ⟨rfl, rfl⟩

private def firstExit : Transfer Atom := FiniteCFG.packedTreeOutput (0, .unit)

private def entryLoopTrace : Trace Events (Transfer Atom) :=
  .exchange (.ask (pollKey first first)) (.inl second)
    (.exchange (.ask (pollKey second second)) (.inr first) (.result firstExit))

/-- The entry case payload supplies the first request. The first reply
changes the next request on the backedge, and the second reply exits. -/
theorem branch_enters_cycle :
    HasTrace (writtenBranch (.inl first) second) entryLoopTrace ∧
      HasTrace (branchPublic.packed.observe (branchEnv (.inl first) second)
        (branchRecord (.inl first) second)) entryLoopTrace := by
  rw [branch_agreement (.inl first) second, branch_packed_state (.inl first) second]
  have enter : branchDispatcher.step (branchDispatcher.start 0 (callerPacket (.inl first) second)) =
      .inr (branchRow first) := rfl
  have request (input : Denote bit) : branchDispatcher.step (branchRow input) =
      .inl (.request (pollKey input input) (branchResume input)) := rfl
  have again : branchDispatcher.step (branchResume first (.inl second)) = .inr (branchRow second) := rfl
  have exit : branchDispatcher.step (branchResume second (.inr first)) = .inr ⟨⟨.inr 0, ⟨⟩⟩⟩ := rfl
  have trace : HasTrace (runState branchDispatcher (branchDispatcher.start 0 (callerPacket (.inl first) second)))
      entryLoopTrace := by
    unfold entryLoopTrace
    rw [run_jump branchDispatcher enter, run_request branchDispatcher _ _ (request first)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump branchDispatcher again, run_request branchDispatcher _ _ (request second)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump branchDispatcher exit, run_result branchDispatcher (result := ⟨⟨0, ⟨⟩⟩⟩) rfl]
    exact out_ret _
  exact ⟨trace, trace⟩


private def entryChoice : PacketType := .coprod replyType bit
private def effectContext : BoundCtx PacketType 2 := .snoc (.snoc .nil bit) entryChoice
private def effectPackets (i : Fin 2) : PacketType := if i.val = 0 then bit else replyType

-- Two enclosing case binders precede the selected request. Its argument
-- uses the inner payload and a saved capture. Its right reply can return
-- the original inner payload, while its left reply feeds the old cycle.
private def effectPolling : FiniteCFG Bool 2 2 2 where
  entry := .case (.bv 0)
    (.case (.bv 0)
      (.let₁ (.op true (.pair (.bv 0) (.bv 3)))
        (.case (.bv 0) (.br 0 (.bv 0)) (.br 3 (.pair (.bv 0) (.bv 2)))))
      (.br 2 .unit))
    (.br 3 (.pair (.bv 0) (.bv 2)))
  block i := if i.val = 0 then
    .let₁ (.op true (.pair (.bv 0) (.bv 0))) (.br 1 (.bv 0))
  else
    .case (.bv 0) (.br 0 (.bv 0)) (.br 2 .unit)

private def effectBuilt : EffectfulEntry.Compiled sig effectContext effectPackets exits effectPolling :=
  (EffectfulEntry.compile sig effectContext effectPackets exits effectPolling [false, false]).get (by decide)

private def effectPublic := effectBuilt.publicReadback
private def effectDispatcher := effectPublic.program

example : (effectPublic.packed.target.block ((2 : Fin 5).cast effectPublic.provenance.count)).erase =
    .let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1)
      (.let₁ (.op true (.pair (.var 4) (.var 1))) (.br 3 (.pair (.var 7) (.var 0)))))) :=
  (Constructed.row_erasure sig _ exits effectPublic 2).symm.trans rfl

example : (effectPublic.packed.target.block ((3 : Fin 5).cast effectPublic.provenance.count)).erase =
    .let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1)
      (.case (.var 6) (.br 0 (.var 0)) (.br 6 (.pair (.var 0) (.var 5))))))) :=
  (Constructed.row_erasure sig _ exits effectPublic 3).symm.trans rfl

-- A second primitive in the selected leaf and an effect in an off-path
-- arm are both outside the admitted grammar.
example : (EffectfulEntry.read sig effectPackets exits [bit] []
    (.let₁ (.op false (.var 0)) (.let₁ (.op false (.var 0)) (.br 0 (.var 0))))).isNone = true := rfl

example : (EffectfulEntry.read sig effectPackets exits [replyType] [false]
    (.case (.var 0) (.let₁ (.op false (.var 0)) (.br 0 (.var 0)))
      (.let₁ (.op false (.var 0)) (.br 0 (.var 0))))).isNone = true := rfl

private def effectEnv (choice : Denote entryChoice) (saved : Denote bit) : Env Atom
  | 0 => entryChoice.encode choice
  | _ => bit.encode saved

private def effectRecord (choice : Denote entryChoice) (saved : Denote bit) : Env Atom :=
  fun _ => NamedFlat.Capture.packEnv 2 (effectEnv choice saved)

private def effectPacket (choice : Denote entryChoice) (saved : Denote bit) :
    Denote (BranchEntry.profile effectContext effectBuilt.outlined.selection.request.profile effectPublic.start) :=
  ((⟨⟩, saved), choice)

private noncomputable def effectWritten (choice : Denote entryChoice) (saved : Denote bit) :
    Tree Events (Transfer Atom) :=
  resultCodec id <$> (region sig.primitive (effectEnv choice saved) effectPolling.erase >>=
    fun out => pure (FiniteCFG.packedTreeOutput out))

private theorem effect_agreement (choice : Denote entryChoice) (saved : Denote bit) :
    effectWritten choice saved = effectPublic.packed.observe (effectEnv choice saved) (effectRecord choice saved) :=
  effectBuilt.public_run (effectEnv choice saved) _ _ id primitivesAgree (codec_id _).symm

private theorem effect_packed_state (choice : Denote entryChoice) (saved : Denote bit) :
    effectPublic.packed.observe (effectEnv choice saved) (effectRecord choice saved) =
      runState effectDispatcher (effectDispatcher.start 0 (effectPacket choice saved)) := by
  rw [effectPublic.packed.observe_eq (effectPacket choice saved) _ _ (fun _ => rfl)]
  change (effectDispatcher.observe 0 (effectPacket choice saved) >>= fun out =>
    pure (FiniteCFG.packedTreeOutput out)) = _
  rw [effectDispatcher.observe_eq 0 (effectPacket choice saved)]
  simp only [runState, bind_assoc, pure_bind]

/-- Bypassing the selected leaf returns at the second outward exit
with the caller payload and saved capture, with no primitive request. -/
theorem effectful_entry_bypass (payload saved : Denote bit) :
    effectWritten (.inr payload) saved = pure (output payload saved) ∧
      effectPublic.packed.observe (effectEnv (.inr payload) saved) (effectRecord (.inr payload) saved) =
        pure (output payload saved) := by
  rw [effect_agreement (.inr payload) saved, effect_packed_state (.inr payload) saved]
  have bypass : effectDispatcher.step (effectDispatcher.start 0 (effectPacket (.inr payload) saved)) =
      .inr ⟨⟨.inr 1, (payload, saved)⟩⟩ := rfl
  rw [run_jump effectDispatcher bypass,
    run_result effectDispatcher (result := ⟨⟨1, (payload, saved)⟩⟩) rfl]
  exact ⟨rfl, rfl⟩

private def effectChoice : Denote entryChoice := .inl (.inl first)

private def effectStart : effectDispatcher.State :=
  effectDispatcher.start 0 (effectPacket effectChoice second)

private def effectLeaf : effectDispatcher.State := by
  refine ⟨⟨.inl ⟨2, by decide⟩, ?_⟩⟩
  change ((Denote bit × Denote entryChoice) × Denote replyType) × Denote bit
  exact (((second, effectChoice), .inl first), first)

private def effectReply (reply : Denote replyType) : effectDispatcher.State := by
  refine ⟨⟨.inl ⟨3, by decide⟩, ?_⟩⟩
  change (((Denote bit × Denote entryChoice) × Denote replyType) × Denote bit) × Denote replyType
  exact ((((second, effectChoice), .inl first), first), reply)

private def effectOld (input : Denote bit) : effectDispatcher.State := by
  refine ⟨⟨.inl ⟨0, by decide⟩, ?_⟩⟩
  change Denote bit
  exact input

private def effectOldReply (reply : Denote replyType) : effectDispatcher.State := by
  refine ⟨⟨.inl ⟨1, by decide⟩, ?_⟩⟩
  change Denote replyType
  exact reply

private theorem effect_enter : effectDispatcher.step effectStart = .inr effectLeaf := rfl

private theorem effect_request :
    effectDispatcher.step effectLeaf = .inl (.request (pollKey first second) effectReply) := rfl

private theorem old_request (input : Denote bit) :
    effectDispatcher.step (effectOld input) = .inl (.request (pollKey input input) effectOldReply) := rfl

private def effectCycleTrace : Trace Events (Transfer Atom) :=
  .exchange (.ask (pollKey first second)) (.inl second)
    (.exchange (.ask (pollKey second second)) (.inl first)
      (.exchange (.ask (pollKey first first)) (.inr second) (.result firstExit)))

/-- The entry request sees the two bound operands. Its left reply passes
the reply payload to the old cycle, which takes a backedge before exiting. -/
theorem effectful_entry_cycle :
    HasTrace (effectWritten effectChoice second) effectCycleTrace ∧
      HasTrace (effectPublic.packed.observe (effectEnv effectChoice second)
        (effectRecord effectChoice second)) effectCycleTrace := by
  rw [effect_agreement, effect_packed_state]
  have intoCycle : effectDispatcher.step (effectReply (.inl second)) = .inr (effectOld second) := rfl
  have backedge : effectDispatcher.step (effectOldReply (.inl first)) = .inr (effectOld first) := rfl
  have exit : effectDispatcher.step (effectOldReply (.inr second)) = .inr ⟨⟨.inr 0, ⟨⟩⟩⟩ := rfl
  have trace : HasTrace (runState effectDispatcher effectStart) effectCycleTrace := by
    unfold effectCycleTrace
    rw [run_jump effectDispatcher effect_enter, run_request effectDispatcher _ _ effect_request]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump effectDispatcher intoCycle, run_request effectDispatcher _ _ (old_request second)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump effectDispatcher backedge, run_request effectDispatcher _ _ (old_request first)]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump effectDispatcher exit, run_result effectDispatcher (result := ⟨⟨0, ⟨⟩⟩⟩) rfl]
    exact out_ret _
  exact ⟨trace, trace⟩

private def effectOutwardTrace : Trace Events (Transfer Atom) :=
  .exchange (.ask (pollKey first second)) (.inr second) (.result (output second first))

/-- The other reply returns at the second outward exit with its own
payload and the entry leaf's original case payload. -/
theorem effectful_entry_reply_exits :
    HasTrace (effectWritten effectChoice second) effectOutwardTrace ∧
      HasTrace (effectPublic.packed.observe (effectEnv effectChoice second)
        (effectRecord effectChoice second)) effectOutwardTrace := by
  rw [effect_agreement, effect_packed_state]
  have exit : effectDispatcher.step (effectReply (.inr second)) = .inr ⟨⟨.inr 1, (second, first)⟩⟩ := rfl
  have trace : HasTrace (runState effectDispatcher effectStart) effectOutwardTrace := by
    unfold effectOutwardTrace
    rw [run_jump effectDispatcher effect_enter, run_request effectDispatcher _ _ effect_request]
    erw [hasTrace_vis_exchange_iff]
    rw [run_jump effectDispatcher exit, run_result effectDispatcher (result := ⟨⟨1, (second, first)⟩⟩) rfl]
    exact out_ret _
  exact ⟨trace, trace⟩


private def multiChoice : PacketType := .coprod bit replyType
private def multiContext : BoundCtx PacketType 1 := .snoc .nil multiChoice

-- The left leaf captures a bit and routes its sum reply into an old row.
-- The other request is under a second binder and returns a bit reply
-- alongside that binder's payload. The remaining arm bypasses both.
private def multiPolling : FiniteCFG Bool 1 2 1 where
  entry := .case (.bv 0)
    (.let₁ (.op true (.pair (.bv 0) (.bv 0)))
      (.case (.bv 0) (.br 0 (.bv 0)) (.br 2 (.pair (.bv 0) (.bv 2)))))
    (.case (.bv 0)
      (.let₁ (.op false (.bv 0)) (.br 2 (.pair (.bv 0) (.bv 1))))
      (.br 2 (.pair (.bv 0) (.bv 0))))
  block _ := .br 1 .unit

private def multiBuild :=
  EffectfulEntry.Multiple.compile sig multiContext packets exits multiPolling

private def multiBuilt : EffectfulEntry.Multiple.Compiled sig multiContext packets exits multiPolling :=
  multiBuild.get (by decide +kernel)

example : multiBuilt.outlined.count = 4 := by decide +kernel

-- Compare the actual packed erasure at each request label with its
-- literal row, including the distinct continuation labels.
private def packedRowMatches {F : Type} [DecidableEq F] {blocks exits captures : Nat}
    {signature : PrimitiveSignature F}
    {context : BoundCtx PacketType captures} {inputs : Fin blocks → PacketType} {outputs : Fin exits → PacketType}
    {source : FiniteCFG F blocks exits captures}
    (build : Option (EffectfulEntry.Multiple.Compiled signature context inputs outputs source))
    (index : Nat) (expected : LambdaSSA.Region F) : Bool :=
  match build with
  | none => false
  | some built =>
    let count := blocks + built.outlined.count + 1
    if bound : index < count then
      let label := (⟨index, bound⟩ : Fin count).cast built.publicReadback.provenance.count
      let publicRow := built.publicReadback.packed.target.block label
      (commonRow (count + exits) publicRow.erase expected).isSome
    else false

example : packedRowMatches multiBuild 1
    (.let₂ (.var 0) (.let₁ (.op true (.pair (.var 0) (.var 0))) (.br 2 (.pair (.var 3) (.var 0))))) = true :=
  by decide +kernel

example : packedRowMatches multiBuild 3
    (.let₂ (.var 0) (.let₂ (.var 1) (.let₁ (.op false (.var 2)) (.br 4 (.pair (.var 5) (.var 0)))))) = true :=
  by decide +kernel

-- A reply continuation may also request directly without a case.
example : (EffectfulEntry.Multiple.read sig packets exits [replyType]
    (.case (.var 0) (.let₁ (.op false (.var 0)) (.let₁ (.op false (.var 0)) (.br 0 (.var 0))))
      (.br 1 .unit))).isSome = true := rfl

-- A computed request operand remains outside the structural operand grammar.
example : (EffectfulEntry.Multiple.read sig packets exits [bit]
    (.let₁ (.op false (.op false (.var 0))) (.br 0 (.var 0)))).isNone = true := rfl

private def multiEnv (choice : Denote multiChoice) : Env Atom := fun _ => multiChoice.encode choice

private def multiRecord (choice : Denote multiChoice) : Env Atom :=
  fun _ => NamedFlat.Capture.packEnv 1 (multiEnv choice)

private noncomputable def multiWritten (choice : Denote multiChoice) : Tree Events (Transfer Atom) :=
  resultCodec id <$> (region sig.primitive (multiEnv choice) multiPolling.erase >>=
    fun out => pure (FiniteCFG.packedTreeOutput out))

private theorem multi_agreement (built : EffectfulEntry.Multiple.Compiled sig multiContext packets exits multiPolling)
    (choice : Denote multiChoice) :
    multiWritten choice = built.publicReadback.packed.observe (multiEnv choice) (multiRecord choice) :=
  built.public_run (multiEnv choice) _ _ id primitivesAgree (codec_id _).symm

private def multiBypass (payload : Denote bit) : Denote multiChoice := .inr (.inr payload)

section Observations

variable (built : EffectfulEntry.Multiple.Compiled sig multiContext packets exits multiPolling)

/-- The pure arm bypasses both requests and returns at the second exit. -/
theorem multiple_entry_bypass (payload : Denote bit) :
    multiWritten (multiBypass payload) = pure (output payload payload) ∧
      built.publicReadback.packed.observe (multiEnv (multiBypass payload)) (multiRecord (multiBypass payload)) =
        pure (output payload payload) := by
  have source : multiWritten (multiBypass payload) = pure (output payload payload) := by
    simp [multiWritten, multiBypass, multiPolling, FiniteCFG.erase, LambdaSSA.Flat.erase, Morphism.CaseSSA.erase,
      region, multiEnv, multiChoice, PacketType.encode, replyType, LambdaSSA.Semantics.Interaction.term,
      LambdaSSA.Semantics.Interaction.splitTransfer, output, resultCodec, codec_id]
  exact ⟨source, (multi_agreement built _).symm.trans source⟩

private def multiLeft : Denote multiChoice := .inl first
private def multiRight : Denote multiChoice := .inr (.inl second)

private def multiLeftTrace : Trace Events (Transfer Atom) :=
  .exchange (.ask (pollKey first first)) (.inl second) (.result firstExit)

private def multiRightTrace : Trace Events (Transfer Atom) :=
  .exchange (.ask (primeKey second)) first (.result (output first second))

private theorem poll_read :
    sig.primitive true (.pair (bit.encode first) (bit.encode first)) =
      vis (.ask (pollKey first first)) (fun (reply : sig.Reply (pollKey first first)) => pure (replyType.encode reply)) := rfl

private theorem prime_read :
    sig.primitive false (bit.encode second) =
      vis (.ask (primeKey second)) (fun (reply : sig.Reply (primeKey second)) => pure (bit.encode reply)) := rfl

private theorem left_entry :
    region sig.primitive (multiEnv multiLeft) multiPolling.entry.erase =
      vis (.ask (pollKey first first)) (fun (reply : sig.Reply (pollKey first first)) => region sig.primitive
        (LambdaSSA.Semantics.extend (LambdaSSA.Semantics.extend (multiEnv multiLeft) (bit.encode first))
          (replyType.encode reply))
        (.case (.var 0) (.br 0 (.var 0)) (.br 2 (.pair (.var 0) (.var 2))))) := by
  simp only [multiPolling, LambdaSSA.Flat.erase, Morphism.CaseSSA.erase, region,
    LambdaSSA.Semantics.Interaction.term, pure_bind]
  change (sig.primitive true (.pair (bit.encode first) (bit.encode first)) >>= _) = _
  rw [poll_read, vis_bind]
  simp only [pure_bind]
  rfl

private theorem right_entry :
    region sig.primitive (multiEnv multiRight) multiPolling.entry.erase =
      vis (.ask (primeKey second)) (fun (reply : sig.Reply (primeKey second)) => pure (2, .pair (bit.encode reply) (bit.encode second))) := by
  simp only [multiPolling, LambdaSSA.Flat.erase, Morphism.CaseSSA.erase, region,
    LambdaSSA.Semantics.Interaction.term, pure_bind]
  change (sig.primitive false (bit.encode second) >>= _) = _
  rw [prime_read, vis_bind]
  simp only [pure_bind]
  rfl

theorem multiple_entry_left : HasTrace (multiWritten multiLeft) multiLeftTrace ∧
      HasTrace (built.publicReadback.packed.observe (multiEnv multiLeft) (multiRecord multiLeft)) multiLeftTrace := by
  have trace : HasTrace (multiWritten multiLeft) multiLeftTrace := by
    unfold multiWritten multiLeftTrace
    rw [show multiPolling.erase = .cfg multiPolling.entry.erase 1 (fun i => (multiPolling.block i).erase) from rfl,
      region, left_entry]
    simp only [map_eq_pure_bind, bind_assoc, vis_bind]
    erw [hasTrace_vis_exchange_iff]
    let step (p : LambdaSSA.Semantics.Interaction.BlockInput Atom 1) :
        Tree Events (Transfer Atom ⊕ LambdaSSA.Semantics.Interaction.BlockInput Atom 1) :=
      region sig.primitive (LambdaSSA.Semantics.extend (multiEnv multiLeft) p.2) (multiPolling.block p.1).erase >>=
        fun out => pure (LambdaSSA.Semantics.Interaction.splitTransfer 1 out)
    have oldExit : Elgot.ITree.iterate step (0, bit.encode second) = pure (0, .unit) := by
      change Elgot.iter step (0, bit.encode second) = _
      rw [congrFun (iterate_fixpoint step) (0, bit.encode second)]
      simp [step, multiPolling, LambdaSSA.Flat.erase, Morphism.CaseSSA.erase, region,
        LambdaSSA.Semantics.Interaction.term, LambdaSSA.Semantics.Interaction.splitTransfer]
    have routed :
        region sig.primitive (LambdaSSA.Semantics.extend
          (LambdaSSA.Semantics.extend (multiEnv multiLeft) (bit.encode first)) (replyType.encode (.inl second)))
          (.case (.var 0) (.br 0 (.var 0)) (.br 2 (.pair (.var 0) (.var 2)))) =
          pure (0, bit.encode second) := by
      simp [region, LambdaSSA.Semantics.Interaction.term, replyType, PacketType.encode]
    rw [routed, pure_bind]
    change HasTrace (Elgot.ITree.iterate step (0, bit.encode second) >>= _) _
    rw [oldExit]
    simp only [pure_bind]
    exact out_ret _
  exact ⟨trace, by rw [← multi_agreement built]; exact trace⟩

theorem multiple_entry_right : HasTrace (multiWritten multiRight) multiRightTrace ∧
      HasTrace (built.publicReadback.packed.observe (multiEnv multiRight) (multiRecord multiRight)) multiRightTrace := by
  have trace : HasTrace (multiWritten multiRight) multiRightTrace := by
    unfold multiWritten multiRightTrace
    rw [show multiPolling.erase = .cfg multiPolling.entry.erase 1 (fun i => (multiPolling.block i).erase) from rfl,
      region, right_entry]
    simp only [map_eq_pure_bind, bind_assoc, vis_bind]
    erw [hasTrace_vis_exchange_iff]
    simp [LambdaSSA.Semantics.Interaction.splitTransfer, resultCodec, codec_id]
    exact out_ret _
  exact ⟨trace, by rw [← multi_agreement built]; exact trace⟩

end Observations

example := multiple_entry_bypass multiBuilt
example := multiple_entry_left multiBuilt
example := multiple_entry_right multiBuilt

private def recursiveSig : PrimitiveSignature Bool :=
  ⟨fun _ => .product bit bit, fun op => if op then replyType else bit⟩
private abbrev RecursiveEvents := Event recursiveSig.Request recursiveSig.Reply

-- A positive reply enables a second opcode using the case payload and
-- the original capture. The other reply returns at the second exit.
private def recursivePolling : FiniteCFG Bool 1 2 1 where
  entry := .let₁ (.op true (.pair (.bv 0) (.bv 0)))
    (.case (.bv 0)
      (.let₁ (.op false (.pair (.bv 0) (.bv 2))) (.br 0 (.bv 0)))
      (.br 2 (.pair (.bv 0) (.bv 2))))
  block _ := .br 1 .unit

private def recursiveBuild :=
  EffectfulEntry.Multiple.compile recursiveSig (.snoc .nil bit) packets exits recursivePolling

private def recursiveBuilt : EffectfulEntry.Multiple.Compiled recursiveSig (.snoc .nil bit) packets exits
    recursivePolling := recursiveBuild.get (by decide +kernel)

example : recursiveBuilt.outlined.count = 4 := by decide +kernel

example : packedRowMatches recursiveBuild 1
    (.let₁ (.op true (.pair (.var 0) (.var 0))) (.br 2 (.pair (.var 1) (.var 0)))) = true :=
  by decide +kernel

example : packedRowMatches recursiveBuild 2
    (.let₂ (.var 0) (.case (.var 0)
      (.br 3 (.pair (.pair (.var 2) (.var 1)) (.var 0))) (.br 7 (.pair (.var 0) (.var 2))))) = true :=
  by decide +kernel

example : packedRowMatches recursiveBuild 3
    (.let₂ (.var 0) (.let₂ (.var 1)
      (.let₁ (.op false (.pair (.var 2) (.var 1))) (.br 4 (.pair (.var 5) (.var 0)))))) = true :=
  by decide +kernel

example : packedRowMatches recursiveBuild 4
    (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1) (.br 0 (.var 4))))) = true :=
  by decide +kernel

private def initialKey : recursiveSig.Request := ⟨true, (first, first)⟩
private def secondaryKey (payload : Denote bit) : recursiveSig.Request := ⟨false, (payload, first)⟩

private theorem recursive_primitive_agreement : PrimitivesAgree recursiveSig.primitive recursiveSig.primitive id := by
  intro op value
  rw [codec_id, show valueCodec (id : Atom → Atom) = id from funext codec_id, id_map]

private theorem recursive_vis_congr (key : recursiveSig.Request)
    {left right : recursiveSig.Reply key → Tree RecursiveEvents (Transfer Atom)}
    (agree : ∀ reply, left reply = right reply) :
    vis (.ask key) left = vis (.ask key) right := congrArg (vis (.ask key)) (funext agree)

private theorem secondary_call (payload : Denote bit) :
    recursiveSig.primitive false (.pair (bit.encode payload) (bit.encode first)) =
      vis (.ask (secondaryKey payload))
        (fun (reply : recursiveSig.Reply (secondaryKey payload)) => pure (bit.encode reply)) := by
  let argument : Denote (recursiveSig.argument false) := (payload, first)
  change recursiveSig.primitive false ((recursiveSig.argument false).encode argument) = _
  unfold PrimitiveSignature.primitive
  rw [Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PacketType.decode_encode
    (recursiveSig.argument false) argument]
  rfl

private theorem recursive_entry :
    region recursiveSig.primitive (env first) recursivePolling.entry.erase =
      vis (.ask initialKey) (fun (reply : recursiveSig.Reply initialKey) =>
        match reply with
        | .inl payload => vis (.ask (secondaryKey payload))
            (fun (next : recursiveSig.Reply (secondaryKey payload)) => pure (0, bit.encode next))
        | .inr payload => pure (2, .pair (bit.encode payload) (bit.encode first))) := by
  simp only [recursivePolling, LambdaSSA.Flat.erase, Morphism.CaseSSA.erase, region,
    LambdaSSA.Semantics.Interaction.term, pure_bind]
  have initial :
      recursiveSig.primitive true (.pair (bit.encode first) (bit.encode first)) =
        vis (.ask initialKey) (fun (reply : recursiveSig.Reply initialKey) => pure (replyType.encode reply)) := rfl
  change (recursiveSig.primitive true (.pair (bit.encode first) (bit.encode first)) >>= _) = _
  rw [initial, vis_bind]
  simp only [pure_bind]
  apply recursive_vis_congr initialKey
  intro reply
  cases reply with
  | inl payload =>
    change (recursiveSig.primitive false (.pair (bit.encode payload) (bit.encode first)) >>= _) = _
    rw [secondary_call, vis_bind]
    simp only [pure_bind]
    rfl
  | inr payload => rfl

private noncomputable def recursiveWritten : Tree RecursiveEvents (Transfer Atom) :=
  resultCodec id <$> (region recursiveSig.primitive (env first) recursivePolling.erase >>=
    fun out => pure (FiniteCFG.packedTreeOutput out))

private noncomputable def recursiveExpected : Tree RecursiveEvents (Transfer Atom) :=
  vis (.ask initialKey) fun (reply : recursiveSig.Reply initialKey) =>
    match reply with
    | .inl payload => vis (.ask (secondaryKey payload)) (fun _ => pure firstExit)
    | .inr payload => pure (output payload first)

/-- The full source tree exposes the second request only on the selected
reply arm. That arm uses the older capture and reaches exit zero through
the existing block. The bypass uses the reply payload at exit one. -/
private theorem recursive_source : recursiveWritten = recursiveExpected := by
  unfold recursiveWritten recursiveExpected
  rw [show recursivePolling.erase = .cfg recursivePolling.entry.erase 1
    (fun i => (recursivePolling.block i).erase) from rfl, region, recursive_entry]
  simp only [map_eq_pure_bind, bind_assoc, vis_bind]
  apply recursive_vis_congr initialKey
  intro reply
  cases reply with
  | inl payload =>
    simp only [vis_bind, pure_bind]
    apply recursive_vis_congr (secondaryKey payload)
    intro next
    let step (p : LambdaSSA.Semantics.Interaction.BlockInput Atom 1) :
        Tree RecursiveEvents (Transfer Atom ⊕ LambdaSSA.Semantics.Interaction.BlockInput Atom 1) :=
      region recursiveSig.primitive (LambdaSSA.Semantics.extend (env first) p.2)
        (recursivePolling.block p.1).erase >>=
        fun out => pure (LambdaSSA.Semantics.Interaction.splitTransfer 1 out)
    have oldExit : Elgot.ITree.iterate step (0, bit.encode next) = pure (0, .unit) := by
      change Elgot.iter step (0, bit.encode next) = _
      rw [congrFun (iterate_fixpoint step) (0, bit.encode next)]
      simp [step, recursivePolling, LambdaSSA.Flat.erase, Morphism.CaseSSA.erase, region,
        LambdaSSA.Semantics.Interaction.term, LambdaSSA.Semantics.Interaction.splitTransfer]
    change (Elgot.ITree.iterate step (0, bit.encode next) >>= _) = _
    rw [oldExit]
    simp only [pure_bind]
    rfl
  | inr payload =>
    simp [LambdaSSA.Semantics.Interaction.splitTransfer, output, resultCodec, codec_id]

private def recursiveRecord : Env Atom := fun _ => NamedFlat.Capture.packEnv 1 (env first)

theorem recursive_packed
    (built : EffectfulEntry.Multiple.Compiled recursiveSig (.snoc .nil bit) packets exits recursivePolling) :
    built.publicReadback.packed.observe (env first) recursiveRecord = recursiveExpected :=
  (built.public_run (env first) _ _ id recursive_primitive_agreement (codec_id _).symm).symm.trans recursive_source

example := recursive_packed recursiveBuilt

open EffectfulEntry.Multiple.Computed (Operand)

-- The first effect is still written inside the outer request's argument.
-- The outward leaf also reads the older capture across the outer reply
-- binder and its case binder.
private def computedPolling : FiniteCFG Bool 1 2 1 where
  entry := .let₁ (.op true (.pair (.op false (.pair (.bv 0) (.bv 0))) (.bv 0)))
    (.case (.bv 0) (.br 0 (.bv 0)) (.br 2 (.pair (.bv 0) (.bv 2))))
  block := recursivePolling.block

private def computedBuild :=
  EffectfulEntry.Multiple.Computed.compile recursiveSig (.snoc .nil bit) packets exits computedPolling

private def computedBuilt :
    EffectfulEntry.Multiple.Computed.Compiled recursiveSig (.snoc .nil bit) packets exits computedPolling :=
  computedBuild.get (by decide +kernel)

private def computedRowMatches (index : Nat) (expected : LambdaSSA.Region Bool) : Bool :=
  match computedBuild with
  | none => false
  | some built => packedRowMatches (some built.checked) index expected

example : computedRowMatches 1
    (.let₁ (.op false (.pair (.var 0) (.var 0))) (.br 2 (.pair (.var 1) (.var 0)))) = true :=
  by decide +kernel

example : computedRowMatches 2 (.let₂ (.var 0) (.br 3 (.pair (.var 1) (.var 0)))) = true :=
  by decide +kernel

example : computedRowMatches 3
    (.let₂ (.var 0) (.let₁ (.op true (.pair (.var 0) (.var 1))) (.br 4 (.pair (.var 3) (.var 0))))) = true :=
  by decide +kernel

example : computedRowMatches 4
    (.let₂ (.var 0) (.let₂ (.var 1)
      (.case (.var 2) (.br 0 (.var 0)) (.br 7 (.pair (.var 0) (.var 2)))))) = true :=
  by decide +kernel

-- The initializer is checked before adding the binder. The body
-- synthesizes its result in the extended scope.
example : (EffectfulEntry.Multiple.Computed.readOperand recursiveSig []
    (.let₁ .unit (.var 0))).map (fun checked => checked.1) = some .unit := rfl

example : (EffectfulEntry.Multiple.Computed.readOperand recursiveSig []
    (.let₁ (.var 0) (.var 0))).isNone = true := rfl

example : (EffectfulEntry.Multiple.Computed.readOperand recursiveSig [bit]
    (.let₂ (.var 0) (.var 0))).isNone = true := rfl

private def outerKey (innerReply : Denote bit) : recursiveSig.Request := ⟨true, (innerReply, first)⟩

private theorem outer_call (innerReply : Denote bit) :
    recursiveSig.primitive true (.pair (bit.encode innerReply) (bit.encode first)) =
      vis (.ask (outerKey innerReply))
        (fun (reply : recursiveSig.Reply (outerKey innerReply)) => pure (replyType.encode reply)) := by
  let argument : Denote (recursiveSig.argument true) := (innerReply, first)
  change recursiveSig.primitive true ((recursiveSig.argument true).encode argument) = _
  unfold PrimitiveSignature.primitive
  rw [Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PacketType.decode_encode
    (recursiveSig.argument true) argument]
  rfl

private def computedArgument : Operand recursiveSig [bit] (.product bit bit) :=
  .pair (.call false (.pure (.pair (.var .here) (.var .here)))) (.pure (.var .here))

private theorem computed_entry :
    region recursiveSig.primitive (env first) computedPolling.entry.erase =
      vis (.ask (secondaryKey first)) (fun (innerReply : recursiveSig.Reply (secondaryKey first)) =>
        vis (.ask (outerKey innerReply)) (fun (reply : recursiveSig.Reply (outerKey innerReply)) =>
          match reply with
          | .inl payload => pure (0, bit.encode payload)
          | .inr payload => pure (2, .pair (bit.encode payload) (bit.encode first)))) := by
  change (region recursiveSig.primitive (env first)
    (.let₁ (.op true computedArgument.written) (.case (.var 0)
      (.br 0 (.var 0)) (.br 2 (.pair (.var 0) (.var 2)))))) = _
  have emitted : computedArgument.schedule.term =
      .let₁ (.op false (.pair (.var 0) (.var 0))) (.pair (.var 0) (.var 1)) := rfl
  rw [region, LambdaSSA.Semantics.Interaction.term,
    computedArgument.preserves_run recursiveSig.primitive (env first), emitted,
    LambdaSSA.Semantics.Interaction.term, LambdaSSA.Semantics.Interaction.term]
  have innerArg : LambdaSSA.Semantics.Interaction.term recursiveSig.primitive (env first)
      (.pair (.var 0) (.var 0)) = pure (.pair (bit.encode first) (bit.encode first)) := by
    simp [LambdaSSA.Semantics.Interaction.term, env]
  rw [innerArg, pure_bind]
  change (((recursiveSig.primitive false (.pair (bit.encode first) (bit.encode first)) >>= fun reply =>
    LambdaSSA.Semantics.Interaction.term recursiveSig.primitive (LambdaSSA.Semantics.extend (env first) reply)
      (.pair (.var 0) (.var 1))) >>= recursiveSig.primitive true) >>= _) = _
  rw [secondary_call first]
  simp only [bind_assoc, vis_bind, pure_bind]
  apply recursive_vis_congr (secondaryKey first)
  intro innerReply
  simp only [LambdaSSA.Semantics.Interaction.term, LambdaSSA.Semantics.extend_zero, LambdaSSA.Semantics.extend_succ,
    pure_bind]
  change (recursiveSig.primitive true (.pair (bit.encode innerReply) (bit.encode first)) >>= _) = _
  rw [outer_call innerReply, vis_bind]
  simp only [pure_bind]
  apply recursive_vis_congr (outerKey innerReply)
  intro reply
  cases reply with
  | inl payload => simp [region, LambdaSSA.Semantics.Interaction.term, replyType, PacketType.encode]
  | inr payload => simp [region, LambdaSSA.Semantics.Interaction.term, replyType, PacketType.encode, env]

private noncomputable def computedWritten : Tree RecursiveEvents (Transfer Atom) :=
  resultCodec id <$> (region recursiveSig.primitive (env first) computedPolling.erase >>=
    fun out => pure (FiniteCFG.packedTreeOutput out))

private noncomputable def computedExpected : Tree RecursiveEvents (Transfer Atom) :=
  vis (.ask (secondaryKey first)) fun (innerReply : recursiveSig.Reply (secondaryKey first)) =>
    vis (.ask (outerKey innerReply)) fun (reply : recursiveSig.Reply (outerKey innerReply)) =>
      match reply with
      | .inl _ => pure firstExit
      | .inr payload => pure (output payload first)

/-- The original nested expression calls the inner opcode first. The
outer key sees its reply paired with the older capture, then the original
case routes a typed reply to either ordered exit. -/
private theorem computed_source : computedWritten = computedExpected := by
  unfold computedWritten computedExpected
  rw [show computedPolling.erase = .cfg computedPolling.entry.erase 1
    (fun i => (computedPolling.block i).erase) from rfl, region, computed_entry]
  simp only [map_eq_pure_bind, bind_assoc, vis_bind]
  apply recursive_vis_congr (secondaryKey first)
  intro innerReply
  apply recursive_vis_congr (outerKey innerReply)
  intro reply
  cases reply with
  | inl payload =>
    let step (p : LambdaSSA.Semantics.Interaction.BlockInput Atom 1) :
        Tree RecursiveEvents (Transfer Atom ⊕ LambdaSSA.Semantics.Interaction.BlockInput Atom 1) :=
      region recursiveSig.primitive (LambdaSSA.Semantics.extend (env first) p.2)
        (computedPolling.block p.1).erase >>=
        fun out => pure (LambdaSSA.Semantics.Interaction.splitTransfer 1 out)
    have oldExit : Elgot.ITree.iterate step (0, bit.encode payload) = pure (0, .unit) := by
      change Elgot.iter step (0, bit.encode payload) = _
      rw [congrFun (iterate_fixpoint step) (0, bit.encode payload)]
      simp [step, computedPolling, recursivePolling, LambdaSSA.Flat.erase, Morphism.CaseSSA.erase, region,
        LambdaSSA.Semantics.Interaction.term, LambdaSSA.Semantics.Interaction.splitTransfer]
    simp only [pure_bind]
    change (Elgot.ITree.iterate step (0, bit.encode payload) >>= _) = _
    rw [oldExit]
    simp only [pure_bind]
    rfl
  | inr payload =>
    simp [LambdaSSA.Semantics.Interaction.splitTransfer, output, resultCodec, codec_id]

theorem computed_packed
    (built : EffectfulEntry.Multiple.Computed.Compiled recursiveSig (.snoc .nil bit) packets exits computedPolling) :
    built.checked.publicReadback.packed.observe (env first) recursiveRecord = computedExpected :=
  (built.public_run (env first) _ _ id recursive_primitive_agreement (codec_id _).symm).symm.trans computed_source

example := computed_packed computedBuilt

private def scheduleSig : PrimitiveSignature (Fin 3) :=
  ⟨fun op => if op.val = 2 then .product bit (.product replyType bit) else bit,
    fun op => if op.val = 0 then bit else replyType⟩
private abbrev ScheduleEvents := Event scheduleSig.Request scheduleSig.Reply

-- An application can itself take a scheduled argument at the right type.
example : (EffectfulEntry.Multiple.Computed.readOperand scheduleSig [bit]
    (.op 1 (.op 0 (.var 0)))).isSome = true := rfl

example : (EffectfulEntry.Multiple.Computed.readOperand scheduleSig [bit]
    (.op 1 (.op 1 (.var 0)))).isNone = true := rfl

-- With the written let, the body uses the initializer reply for both
-- the second request's argument and the outer argument's first field.
-- The outer request and its outward continuation also read the capture.
private def schedulePolling (usesLet : Bool) : FiniteCFG (Fin 3) 1 2 1 where
  entry := .let₁ (.op 2 (if usesLet then
    .let₁ (.op 0 (.bv 0)) (.pair (.bv 0) (.pair (.op 1 (.bv 0)) (.bv 1)))
    else .pair (.op 0 (.bv 0)) (.pair (.op 1 (.bv 0)) (.bv 0))))
    (.case (.bv 0) (.br 0 (.bv 0)) (.br 2 (.pair (.bv 0) (.bv 2))))
  block _ := .br 1 .unit

private def scheduleBuild (usesLet : Bool) :=
  EffectfulEntry.Multiple.Computed.compile scheduleSig (.snoc .nil bit) packets exits (schedulePolling usesLet)

private def scheduleBuilt (usesLet : Bool) :
    EffectfulEntry.Multiple.Computed.Compiled scheduleSig (.snoc .nil bit) packets exits (schedulePolling usesLet) :=
  (scheduleBuild usesLet).get (by cases usesLet <;> decide +kernel)

private def scheduleRowMatches (usesLet : Bool) (index : Nat) (expected : LambdaSSA.Region (Fin 3)) : Bool :=
  match scheduleBuild usesLet with
  | none => false
  | some built => packedRowMatches (some built.checked) index expected

example (usesLet : Bool) :
    scheduleRowMatches usesLet 1 (.let₁ (.op 0 (.var 0)) (.br 2 (.pair (.var 1) (.var 0)))) = true :=
  by cases usesLet <;> decide +kernel

example (usesLet : Bool) : scheduleRowMatches usesLet 2 (.let₂ (.var 0) (.br 3 (.pair (.var 1) (.var 0)))) = true :=
  by cases usesLet <;> decide +kernel

example (usesLet : Bool) : scheduleRowMatches usesLet 3
    (.let₂ (.var 0) (.let₁ (.op 1 (.var (if usesLet then 0 else 1))) (.br 4 (.pair (.var 3) (.var 0))))) = true :=
  by cases usesLet <;> decide +kernel

example (usesLet : Bool) : scheduleRowMatches usesLet 4
    (.let₂ (.var 0) (.let₂ (.var 1) (.br 5 (.pair (.pair (.var 1) (.var 0)) (.var 2))))) = true :=
  by cases usesLet <;> decide +kernel

example (usesLet : Bool) : scheduleRowMatches usesLet 5
    (.let₂ (.var 0) (.let₂ (.var 1)
      (.let₁ (.op 2 (.pair (.var 0) (.pair (.var 2) (.var 1)))) (.br 6 (.pair (.var 5) (.var 0)))))) = true :=
  by cases usesLet <;> decide +kernel

example (usesLet : Bool) : scheduleRowMatches usesLet 6
    (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1)
      (.case (.var 4) (.br 0 (.var 0)) (.br 9 (.pair (.var 0) (.var 2))))))) = true :=
  by cases usesLet <;> decide +kernel

private def scheduleLeft : scheduleSig.Request := ⟨0, first⟩
private def scheduleRight (usesLet : Bool) (left : Denote bit) : scheduleSig.Request :=
  ⟨1, if usesLet then left else first⟩
private def scheduleOuter (left : Denote bit) (right : Denote replyType) : scheduleSig.Request :=
  ⟨2, (left, right, first)⟩

private theorem typed_call {F : Type} (signature : PrimitiveSignature F) (key : signature.Request) :
    signature.primitive key.1 ((signature.argument key.1).encode key.2) =
      vis (.ask key) (fun (reply : signature.Reply key) => pure ((signature.reply key.1).encode reply)) := by
  cases key with
  | mk op arg =>
    unfold PrimitiveSignature.primitive
    rw [Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PacketType.decode_encode]

private theorem typed_request_congr {F : Type} (signature : PrimitiveSignature F) (key : signature.Request)
    {left right : signature.Reply key → Tree (Event signature.Request signature.Reply) (Transfer Atom)}
    (agree : ∀ reply, left reply = right reply) :
    vis (.ask key) left = vis (.ask key) right := congrArg (vis (.ask key)) (funext agree)

private def scheduledArgument (usesLet : Bool) : Operand scheduleSig [bit] (scheduleSig.argument 2) :=
  if usesLet then
    .let₁ (.call 0 (.pure (.var .here)))
      (.pair (.pure (.var .here)) (.pair (.call 1 (.pure (.var .here))) (.pure (.var (.there .here)))))
  else .pair (.call 0 (.pure (.var .here))) (.pair (.call 1 (.pure (.var .here))) (.pure (.var .here)))

private theorem scheduled_entry (usesLet : Bool) :
    region scheduleSig.primitive (env first) (schedulePolling usesLet).entry.erase =
      vis (.ask scheduleLeft) (fun (left : scheduleSig.Reply scheduleLeft) =>
        vis (.ask (scheduleRight usesLet left)) (fun (right : scheduleSig.Reply (scheduleRight usesLet left)) =>
          vis (.ask (scheduleOuter left right)) (fun (reply : scheduleSig.Reply (scheduleOuter left right)) =>
            match reply with
            | .inl payload => pure (0, bit.encode payload)
            | .inr payload => pure (2, .pair (bit.encode payload) (bit.encode first))))) := by
  have written : (schedulePolling usesLet).entry.erase = .let₁ (.op 2 (scheduledArgument usesLet).written)
      (.case (.var 0) (.br 0 (.var 0)) (.br 2 (.pair (.var 0) (.var 2)))) := by cases usesLet <;> rfl
  have scheduled : (scheduledArgument usesLet).schedule.term =
      .let₁ (.op 0 (.var 0)) (.let₁ (.op 1 (.var (if usesLet then 0 else 1)))
        (.pair (.var 1) (.pair (.var 0) (.var 2)))) := by cases usesLet <;> rfl
  rw [written, region, LambdaSSA.Semantics.Interaction.term,
    (scheduledArgument usesLet).preserves_run scheduleSig.primitive (env first), scheduled]
  simp only [LambdaSSA.Semantics.Interaction.term, bind_assoc, pure_bind, LambdaSSA.Semantics.extend_zero,
    LambdaSSA.Semantics.extend_succ]
  change (scheduleSig.primitive scheduleLeft.1 ((scheduleSig.argument scheduleLeft.1).encode scheduleLeft.2) >>= _) = _
  rw [typed_call scheduleSig scheduleLeft, vis_bind]
  simp only [pure_bind]
  apply typed_request_congr scheduleSig scheduleLeft
  intro left
  let next := scheduleRight usesLet left
  have argument : LambdaSSA.Semantics.extend (env first) (bit.encode left) (if usesLet then 0 else 1) =
      (scheduleSig.argument next.1).encode next.2 := by cases usesLet <;> rfl
  change (scheduleSig.primitive next.1
    (LambdaSSA.Semantics.extend (env first) (bit.encode left) (if usesLet then 0 else 1)) >>= _) = _
  rw [argument, typed_call scheduleSig next, vis_bind]
  simp only [pure_bind]
  apply typed_request_congr scheduleSig next
  intro right
  let key := scheduleOuter left right
  change (scheduleSig.primitive key.1 ((scheduleSig.argument key.1).encode key.2) >>= _) = _
  rw [typed_call scheduleSig key, vis_bind]
  simp only [pure_bind]
  apply typed_request_congr scheduleSig key
  intro reply
  cases reply with
  | inl payload =>
    change region scheduleSig.primitive (LambdaSSA.Semantics.extend (env first) (.inl (bit.encode payload)))
      (.case (.var 0) (.br 0 (.var 0)) (.br 2 (.pair (.var 0) (.var 2)))) = _
    simp only [region, LambdaSSA.Semantics.Interaction.term, LambdaSSA.Semantics.extend_zero, pure_bind]
  | inr payload =>
    change region scheduleSig.primitive (LambdaSSA.Semantics.extend (env first) (.inr (bit.encode payload)))
      (.case (.var 0) (.br 0 (.var 0)) (.br 2 (.pair (.var 0) (.var 2)))) = _
    simp only [region, LambdaSSA.Semantics.Interaction.term, LambdaSSA.Semantics.extend_zero,
      LambdaSSA.Semantics.extend_succ, pure_bind, env]

private noncomputable def scheduleWritten (usesLet : Bool) : Tree ScheduleEvents (Transfer Atom) :=
  resultCodec id <$> (region scheduleSig.primitive (env first) (schedulePolling usesLet).erase >>=
    fun out => pure (FiniteCFG.packedTreeOutput out))

private noncomputable def scheduleExpected (usesLet : Bool) : Tree ScheduleEvents (Transfer Atom) :=
  vis (.ask scheduleLeft) fun (left : scheduleSig.Reply scheduleLeft) =>
    vis (.ask (scheduleRight usesLet left)) fun (right : scheduleSig.Reply (scheduleRight usesLet left)) =>
      vis (.ask (scheduleOuter left right)) fun (reply : scheduleSig.Reply (scheduleOuter left right)) =>
        match reply with
        | .inl _ => pure firstExit
        | .inr payload => pure (output payload first)

/-- The let initializer makes one request. Its reply supplies the second
request and remains in the outer key with the second reply and capture. -/
private theorem schedule_source (usesLet : Bool) : scheduleWritten usesLet = scheduleExpected usesLet := by
  unfold scheduleWritten scheduleExpected
  rw [show (schedulePolling usesLet).erase = .cfg (schedulePolling usesLet).entry.erase 1
    (fun i => ((schedulePolling usesLet).block i).erase) from rfl, region, scheduled_entry usesLet]
  simp only [map_eq_pure_bind, bind_assoc, vis_bind]
  apply typed_request_congr scheduleSig scheduleLeft
  intro left
  apply typed_request_congr scheduleSig (scheduleRight usesLet left)
  intro right
  apply typed_request_congr scheduleSig (scheduleOuter left right)
  intro reply
  cases reply with
  | inl payload =>
    let step (p : LambdaSSA.Semantics.Interaction.BlockInput Atom 1) :
        Tree ScheduleEvents (Transfer Atom ⊕ LambdaSSA.Semantics.Interaction.BlockInput Atom 1) :=
      region scheduleSig.primitive (LambdaSSA.Semantics.extend (env first) p.2)
        ((schedulePolling usesLet).block p.1).erase >>= fun out => pure (LambdaSSA.Semantics.Interaction.splitTransfer 1 out)
    have oldExit : Elgot.ITree.iterate step (0, bit.encode payload) = pure (0, .unit) := by
      change Elgot.iter step (0, bit.encode payload) = _
      rw [congrFun (iterate_fixpoint step) (0, bit.encode payload)]
      simp [step, schedulePolling, LambdaSSA.Flat.erase, Morphism.CaseSSA.erase, region,
        LambdaSSA.Semantics.Interaction.term, LambdaSSA.Semantics.Interaction.splitTransfer]
    simp only [pure_bind]
    change (Elgot.ITree.iterate step (0, bit.encode payload) >>= _) = _
    rw [oldExit]
    simp only [pure_bind]
    rfl
  | inr payload =>
    simp [LambdaSSA.Semantics.Interaction.splitTransfer, output, resultCodec, codec_id]

theorem schedule_packed (usesLet : Bool)
    (built : EffectfulEntry.Multiple.Computed.Compiled scheduleSig (.snoc .nil bit) packets exits
      (schedulePolling usesLet)) :
    built.checked.publicReadback.packed.observe (env first) recursiveRecord = scheduleExpected usesLet := by
  have primitives : PrimitivesAgree scheduleSig.primitive scheduleSig.primitive id := by
    intro op value
    rw [codec_id, show valueCodec (id : Atom → Atom) = id from funext codec_id, id_map]
  exact (built.public_run (env first) _ _ id primitives (codec_id _).symm).symm.trans (schedule_source usesLet)

example := schedule_packed false (scheduleBuilt false)
example := schedule_packed true (scheduleBuilt true)

private def destructureSig : PrimitiveSignature (Fin 3) :=
  ⟨fun op =>
    if op.val = 0 then bit
    else if op.val = 1 then .product bit bit
    else .product replyType (.product bit (.product replyType bit)),
    fun op => if op.val = 0 then .product bit replyType else if op.val = 1 then bit else replyType⟩
private abbrev DestructureEvents := Event destructureSig.Request destructureSig.Reply

-- Dropping both fields still schedules the initializer once.
example : (EffectfulEntry.Multiple.Computed.readOperand destructureSig [bit]
    (.let₂ (.op 0 (.var 0)) .unit)).map (fun checked => checked.2.schedule.term) =
      some (.let₁ (.op 0 (.var 0)) (.let₂ (.var 0) .unit)) := rfl

-- Slot zero is the sum-valued right field. The later request uses the
-- left field and older capture, while the outer request uses the right
-- field twice, the later reply, and the capture.
private def destructureEntry : FiniteCFG (Fin 3) 1 2 1 where
  entry := .let₁ (.op 2 (.let₂ (.op 0 (.bv 0))
    (.pair (.bv 0) (.pair (.op 1 (.pair (.bv 1) (.bv 2))) (.pair (.bv 0) (.bv 2))))))
    (.case (.bv 0) (.br 0 (.bv 0)) (.br 2 (.pair (.bv 0) (.bv 2))))
  block _ := .br 1 .unit

private def destructureBuild :=
  EffectfulEntry.Multiple.Computed.compile destructureSig (.snoc .nil bit) packets exits destructureEntry

private def destructureBuilt :
    EffectfulEntry.Multiple.Computed.Compiled destructureSig (.snoc .nil bit) packets exits destructureEntry :=
  destructureBuild.get (by decide +kernel)

private def destructureRowMatches (index : Nat) (expected : LambdaSSA.Region (Fin 3)) : Bool :=
  match destructureBuild with
  | none => false
  | some built => packedRowMatches (some built.checked) index expected

example : destructureBuilt.checked.outlined.count = 7 := by decide +kernel

example : destructureRowMatches 1 (.let₁ (.op 0 (.var 0)) (.br 2 (.pair (.var 1) (.var 0)))) = true :=
  by decide +kernel

example : destructureRowMatches 3
    (.let₂ (.var 0) (.let₂ (.var 0)
      (.br 4 (.pair (.pair (.pair (.var 3) (.var 2)) (.var 1)) (.var 0))))) = true :=
  by decide +kernel

example : destructureRowMatches 4
    (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1)
      (.let₁ (.op 1 (.pair (.var 2) (.var 1))) (.br 5 (.pair (.var 7) (.var 0))))))) = true :=
  by decide +kernel

example : destructureRowMatches 6
    (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1)
      (.let₁ (.op 2 (.pair (.var 4) (.pair (.var 6) (.pair (.var 4) (.var 1)))))
        (.br 7 (.pair (.var 9) (.var 0)))))))) = true :=
  by decide +kernel

example : destructureRowMatches 7
    (.let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1) (.let₂ (.var 1)
      (.case (.var 8) (.br 0 (.var 0)) (.br 10 (.pair (.var 0) (.var 2))))))))) = true :=
  by decide +kernel

private def pairRequest : destructureSig.Request := ⟨0, first⟩
private def fieldRequest (left : Denote bit) : destructureSig.Request := ⟨1, (left, first)⟩
private def destructureOuter (right : Denote replyType) (later : Denote bit) : destructureSig.Request :=
  ⟨2, (right, later, right, first)⟩

private noncomputable def destructureExpected : Tree DestructureEvents (Transfer Atom) :=
  vis (.ask pairRequest) fun (fields : destructureSig.Reply pairRequest) =>
    vis (.ask (fieldRequest fields.1)) fun (later : destructureSig.Reply (fieldRequest fields.1)) =>
      vis (.ask (destructureOuter fields.2 later)) fun (reply : destructureSig.Reply (destructureOuter fields.2 later)) =>
        match reply with
        | .inl _ => pure firstExit
        | .inr payload => pure (output payload first)

/-- Reduce the original evaluator's product bind. Even with repeated
field reads, the whole tree asks for the pair exactly once. -/
private theorem destructure_source :
    (resultCodec id <$> (region destructureSig.primitive (env first) destructureEntry.erase >>=
      fun out => pure (FiniteCFG.packedTreeOutput out))) = destructureExpected := by
  unfold destructureExpected
  rw [show destructureEntry.erase = .cfg destructureEntry.entry.erase 1
    (fun i => (destructureEntry.block i).erase) from rfl, region]
  simp only [destructureEntry, LambdaSSA.Flat.erase, Morphism.CaseSSA.erase, region,
    LambdaSSA.Semantics.Interaction.term, map_eq_pure_bind, bind_assoc, pure_bind]
  change (destructureSig.primitive pairRequest.1 ((destructureSig.argument pairRequest.1).encode pairRequest.2) >>= _) = _
  rw [typed_call destructureSig pairRequest, vis_bind]
  apply typed_request_congr destructureSig pairRequest
  rintro ⟨left, right⟩
  let key := fieldRequest left
  have pairReply : (destructureSig.reply pairRequest.1).encode (left, right) =
      .pair (bit.encode left) (replyType.encode right) := rfl
  simp only [pure_bind, pairReply, bind_assoc]
  change (destructureSig.primitive key.1 ((destructureSig.argument key.1).encode key.2) >>= _) = _
  rw [typed_call destructureSig key, vis_bind]
  apply typed_request_congr destructureSig key
  intro later
  let outer := destructureOuter right later
  simp only [pure_bind]
  change (destructureSig.primitive outer.1 ((destructureSig.argument outer.1).encode outer.2) >>= _) = _
  rw [typed_call destructureSig outer, vis_bind]
  apply typed_request_congr destructureSig outer
  intro reply
  have encodeReply : (destructureSig.reply outer.1).encode reply = replyType.encode reply := rfl
  rw [encodeReply]
  cases reply with
  | inl payload =>
    simp [replyType, PacketType.encode, LambdaSSA.Semantics.Interaction.splitTransfer]
    let step (_ : LambdaSSA.Semantics.Interaction.BlockInput Atom 1) :
        Tree DestructureEvents (Transfer Atom ⊕ LambdaSSA.Semantics.Interaction.BlockInput Atom 1) :=
      pure (.inl (0, .unit))
    change (fun out => resultCodec id (FiniteCFG.packedTreeOutput out)) <$>
      Elgot.ITree.iterate step (0, bit.encode payload) = _
    have oldExit : Elgot.ITree.iterate step (0, bit.encode payload) = pure (0, .unit) := by
      change Elgot.iter step (0, bit.encode payload) = _
      rw [congrFun (iterate_fixpoint step) (0, bit.encode payload)]
      simp only [step, pure_bind, Sum.elim_inl]
    rw [oldExit]
    simp only [map_eq_pure_bind, pure_bind, resultCodec, codec_id, firstExit]
  | inr payload =>
    simp [replyType, PacketType.encode, LambdaSSA.Semantics.Interaction.splitTransfer, output, resultCodec, codec_id, env]

theorem destructure_packed
    (built : EffectfulEntry.Multiple.Computed.Compiled destructureSig (.snoc .nil bit) packets exits destructureEntry) :
    built.checked.publicReadback.packed.observe (env first) recursiveRecord = destructureExpected := by
  have primitives : PrimitivesAgree destructureSig.primitive destructureSig.primitive id := by
    intro op value
    rw [codec_id, show valueCodec (id : Atom → Atom) = id from funext codec_id, id_map]
  exact (built.public_run (env first) _ _ id primitives (codec_id _).symm).symm.trans destructure_source

example := destructure_packed destructureBuilt

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.CaseExamples
