module

import Silmaril.Wasm.Game.Intrinsic.Requests.Repeat.Thms
import Silmaril.Wasm.Game.Adequacy.Thms
import Silmaril.Wasm.Validation.Intrinsic.Reify
import Silmaril.Wasm.Verify.Check.Thms
import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun

namespace Silmaril.Wasm.Game.Intrinsic.Requests.Repeat.Example

open Silmaril.Games Execution.Core Numerics SingleThreaded SingleThreaded.Exec Validation

private def sig : FnType := ⟨[], []⟩
private def shellCode : Func := ⟨⟨1⟩, [], []⟩
private def shell : Module where
  types := [⟨[⟨true, [], .func ⟨[.num (.int .i32)], [.num (.int .i32)]⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  imports := [⟨"env", "tick", .func ⟨0⟩⟩]
  funcs := [shellCode]
  exports := [⟨"repeat", .func ⟨1⟩⟩]

private def shape : Validation.Intrinsic.Reify.Reified shell :=
  (Validation.Intrinsic.Reify.reify? shell).get (by decide +kernel)

private def defType : DefType := shape.typed.definedFuncs[0]'(by decide +kernel)
private def header := (Validation.Intrinsic.Reify.reifyFunction? shape.typed.context defType shellCode).get
  (by decide +kernel)

private def bodyContext : Context := shape.typed.context.funcBody header.val.params.toList
  header.val.results.toList header.val.localTypes

private def callBody := (Validation.Intrinsic.Reify.reifyBody? (bodyContext.withLabel []) [] [.i32]
    [.intConst .i32 7, .call ⟨0⟩]).get (by decide +kernel)

private def loopBody : Validation.Intrinsic.Body (bodyContext.withLabel []) (.plain [] []) :=
  .seq callBody.val (by simp) (.single (.brIf (target := []) ⟨⟨0⟩, rfl⟩))

private def implementation : Validation.Intrinsic.Function shape.typed.context defType :=
  { header.val with body := .single (.loop .empty .empty loopBody) }

private def program : Validation.Intrinsic.Module shape.interface :=
  { shape.typed with funcs := .cons implementation .nil }

private def raw : Module := program.erase

example : raw.funcs = [⟨⟨1⟩, [], [.loop .empty [.intConst .i32 7, .call ⟨0⟩, .brIf ⟨0⟩]]⟩] := by
  with_unfolding_all rfl

private def checked : CModuleType × ScalarInstance := (Verify.instance? raw).get (by decide +kernel)
private def instance_ : ScalarInstance := checked.2

private def registered : Registered program where
  instance_ := instance_
  ready := Verify.isInstance_of_instance? (by with_unfolding_all rfl)
  exports := .cons ⟨_, rfl, rfl⟩ .nil

private def store : Store Nat := instance_.store
private def moduleInst : ModuleInst := (store.funcs[1]?.map FuncInst.module).getD {}
private def entry : Entry implementation instance_ store sig :=
  ⟨⟨0, by decide +kernel⟩, rfl, rfl, 1, rfl, moduleInst, by with_unfolding_all rfl⟩

private def request : NamedImport raw instance_ := ⟨⟨0, by decide +kernel⟩, "env", "tick", ⟨0⟩, rfl⟩
private def callArgs : Typed request.signature.params := ⟨[.num ⟨.int .i32, 7⟩], .cons ⟨7, rfl⟩ .nil⟩
private def reply : Typed request.signature.results := ⟨[.num ⟨.int .i32, 1⟩], .cons ⟨1, rfl⟩ .nil⟩
private def args : Typed sig.params := ⟨[], .nil⟩
private def op : instance_.F.Op := entry.question args

private theorem decode : instance_.importOp? request.slot.val callArgs.val = some (request.question callArgs) := by
  unfold ScalarInstance.importOp? ifaceOp?
  split
  · split
    · rfl
    · rename_i _ invalid
      exact False.elim (invalid callArgs.property)
  · rename_i invalid
    exact False.elim (invalid request.slot.isLt)

private def toCallout := runC (stepI neverFail) 16 store (instance_.initThread op)
private def waiting : Thread := toCallout.2.1
private def resumed : Thread := resumeResult store waiting (.values reply.val)

private theorem callout : CalloutAt store waiting request.slot.val callArgs.val := by
  let found := (decompose? store (waiting.config store).code).get (by decide +kernel)
  exact ⟨found.1, found.2.1, by with_unfolding_all rfl⟩

private theorem entry_reaches_typed : ∃ results,
    Reach (profile neverFail) (store, instance_.initThread op) (store, waiting) ∧ ThreadOk store waiting results := by
  obtain ⟨_, _, _, _, _, valid⟩ := invoke_ok registered.ready.ok.storeOk (entry.invokeOk args)
  obtain ⟨reach, typing, _⟩ := runCI_sound_typed 16 store (instance_.initThread op) valid
    (show runC (stepI neverFail) 16 store (instance_.initThread op) = (store, waiting, toCallout.2.2) from
      by with_unfolding_all rfl)
  exact ⟨_, by simpa only [Reach, internalP_profile] using reach, typing⟩

private theorem resumption_typed {results} (typedWaiting : ThreadOk store waiting results)
    (value : Typed request.signature.results) :
    ThreadOk store (resumeResult store waiting (.values value.val)) results :=
  ScalarInstance.resume_answer_typed (profile neverFail) registered.ready.ok typedWaiting callout decode
    (.values value) trivial

/-- The back-edge returns to the exact callout configuration, not just to a
thread with the same status or an equivalent prefix. -/
theorem cycle_realized : Repeat (profile neverFail) request callArgs reply store waiting := by
  obtain ⟨_, _, typedWaiting⟩ := entry_reaches_typed
  have typedResume : ThreadOk store resumed _ := resumption_typed typedWaiting reply
  have reach := (runCI_sound_typed 16 store resumed typedResume
    (show runC (stepI neverFail) 16 store resumed = (store, waiting, toCallout.2.2) from
      by with_unfolding_all rfl)).1
  exact ⟨callout, decode, by simpa only [Reach, internalP_profile, resumed] using reach⟩

private def answering : Env instance_.E := fun question => some (.values ⟨reply.val, by
  have bound := question.1.isLt
  change question.1.val < 1 at bound
  have slot : question.1 = request.slot := Fin.ext (show question.1.val = 0 by omega)
  rw [slot]
  exact reply.property⟩)

private theorem answering_admissible : ThrowsBelow answering store.exns.length := by
  intro question answer selected
  obtain rfl := Option.some.inj selected
  trivial

/-- There is no silent or diverged host outcome on the recurring question. -/
theorem answered_core_trace : ∃ period > 0, ∃ trace : Nat → Config Nat,
    trace 0 = waiting.config store ∧
    (∀ time, Step (profile neverFail) (hostOf instance_.imports answering) (trace time) (trace (time + 1))) ∧
    (∀ time, time % period ≠ 0 → Step (profile neverFail) Det.noHost (trace time) (trace (time + 1))) ∧
    ∀ turn, trace (turn * period) = waiting.config store ∧ trace (turn * period + 1) = resumed.config store :=
  cycle_realized.periodic_core answering rfl

theorem answered_game_prefix (count : Nat) :
    .inr (.ask op) :: .inl (.ask (request.question callArgs)) :: Repeat.moves request callArgs reply count ∈
      instance_.strategy (profile neverFail) store := by
  obtain ⟨_, enter, _⟩ := entry_reaches_typed
  exact cycle_realized.game_prefix enter count

theorem observes_divergence : Behaviour.diverges ∈ entry.denote (profile neverFail) answering args := by
  rw [entry.adequacy registered.ready.ok answering answering_admissible args]
  obtain ⟨_, _, trace, first, step, _, _⟩ := answered_core_trace
  obtain ⟨_, enter, _⟩ := entry_reaches_typed
  exact diverges_mem_behavioursOf_iff.mpr (InfiniteTrace.of_steps (Reach.steps enter) ⟨trace, first, step⟩)

private def stopReply : Typed request.signature.results := ⟨[.num ⟨.int .i32, 0⟩], .cons ⟨0, rfl⟩ .nil⟩

/-- The selected value matters: answering with zero instead leaves the loop
and completes the stock open round rather than producing another request. -/
theorem zero_finishes : ∃ target, entry.round (profile neverFail) args
    [.inl (.ask (request.question callArgs)), .inl (.ans (request.question callArgs) (.values stopReply)),
      .inr (.ans op (.values ⟨[], .nil⟩))] target := by
  obtain ⟨_, enter, typedWaiting⟩ := entry_reaches_typed
  let start := resumeResult store waiting (.values stopReply.val)
  let finish := runC (stepI neverFail) 16 store start
  have last := (runCI_sound_typed (o := neverFail) 16 store start (resumption_typed typedWaiting stopReply)
    (show _ = (finish.1, finish.2.1, finish.2.2) from by simp only [Prod.eta, finish])).1
  have reach : Reach (profile neverFail) (store, start) (finish.1, finish.2.1) := by
    simpa only [Reach, internalP_profile] using last
  have result : ResultAt finish.1 finish.2.1 (.values []) := by with_unfolding_all rfl
  exact ⟨finish.1, .cons (.ucall enter callout decode)
    (.cons (.uret (e := request.question callArgs) (.values stopReply))
      (.cons (.oret reach result (Answer.ofResult?_toResult (.values ⟨[], .nil⟩))) (.nil _))), by simp⟩

end Silmaril.Wasm.Game.Intrinsic.Requests.Repeat.Example
