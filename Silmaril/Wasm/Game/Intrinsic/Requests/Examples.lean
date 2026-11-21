module

import Silmaril.Wasm.Game.Intrinsic.Requests.Thms
import Silmaril.Wasm.Game.Adequacy.Thms
import Silmaril.Wasm.Validation.Intrinsic.Reify
import Silmaril.Wasm.Verify.Check.Thms
import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun

namespace Silmaril.Wasm.Game.Intrinsic.Requests.Examples

open Silmaril.Games Execution.Core Numerics SingleThreaded SingleThreaded.Exec Validation

private def sig : FnType := ⟨[], [.num (.int .i32)]⟩
private def code : Func := ⟨⟨1⟩, [], [.intConst .i32 7, .call ⟨0⟩, .intConst .i32 42]⟩

private def raw : Module where
  types := [⟨[⟨true, [], .func ⟨[.num (.int .i32)], []⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[], [.num (.int .i32)]⟩⟩]⟩]
  imports := [⟨"env", "callback", .func ⟨0⟩⟩]
  funcs := [code]
  exports := [⟨"answer", .func ⟨1⟩⟩]

private def program : Validation.Intrinsic.Reify.Reified raw :=
  (Validation.Intrinsic.Reify.reify? raw).get (by decide +kernel)

private def checked : CModuleType × ScalarInstance := (Verify.instance? raw).get (by decide +kernel)
private def instance_ : ScalarInstance := checked.2

private def registered : Registered program.typed where
  instance_ := instance_
  ready := by
    rw [program.erase_eq]
    exact Verify.isInstance_of_instance? (by rfl)
  exports := .cons ⟨_, rfl, rfl⟩ .nil

private def defType : DefType := program.typed.definedFuncs[0]'(by decide +kernel)
private def typed := (Validation.Intrinsic.Reify.reifyFunction? program.typed.context defType code).get
  (by decide +kernel)
private def implementation : ModuleInst := (instance_.store.funcs[1]?.map FuncInst.module).getD {}
private def entry : Entry typed.val instance_ instance_.store sig :=
  ⟨⟨0, by decide +kernel⟩, rfl, rfl, 1, rfl, implementation, by rw [typed.property]; rfl⟩

private def request : NamedImport program.typed.erase instance_ :=
  ⟨⟨0, by decide +kernel⟩, "env", "callback", ⟨0⟩, by rw [program.erase_eq]; rfl⟩

example : program.typed.erase.imports[request.slot.val]? ≠ some ⟨"env", "missing", .func ⟨0⟩⟩ := by
  change program.typed.erase.imports[0]? ≠ _
  rw [program.erase_eq]
  decide +kernel

private def callbackArgs : Typed request.signature.params := ⟨[.num ⟨.int .i32, 7⟩], .cons ⟨7, rfl⟩ .nil⟩
private def exportArgs : Typed sig.params := ⟨[], .nil⟩
private def op : instance_.F.Op := entry.question exportArgs
private def success : instance_.F.Ar op := .values ⟨[.num ⟨.int .i32, 42⟩], .cons ⟨42, rfl⟩ .nil⟩
private def emptyReply : Answer request.signature := .values ⟨[], .nil⟩

private def after : Answer request.signature → Tree program.typed.erase instance_ (instance_.exports.get op.1)
  | .values _ => .done success
  | .trap => .done .trap
  | .throw address => .done (.throw address)

private def tree := Tree.ask request callbackArgs after

private def before : Thread := instance_.initThread op
private def toCallout := runC (stepI neverFail) 12 instance_.store before
private def waiting : Thread := toCallout.2.1

private theorem decode : instance_.importOp? request.slot.val callbackArgs.val =
    some (request.question callbackArgs) := by
  unfold ScalarInstance.importOp? ifaceOp?
  split
  · split
    · rfl
    · rename_i bound invalid
      exact False.elim (invalid callbackArgs.property)
  · rename_i invalid
    exact False.elim (invalid request.slot.isLt)

private theorem callout : CalloutAt instance_.store waiting request.slot.val callbackArgs.val := by
  let found := (decompose? instance_.store (waiting.config instance_.store).code).get (by decide +kernel)
  exact ⟨found.1, found.2.1, by with_unfolding_all rfl⟩

private theorem prefix_reaches_typed : ∃ results,
    Reach (profile neverFail) (instance_.store, before) (instance_.store, waiting) ∧
    ThreadOk instance_.store waiting results := by
  obtain ⟨_, _, _, _, _, valid⟩ := invoke_ok registered.ready.ok.storeOk (entry.invokeOk exportArgs)
  obtain ⟨run, typing, _⟩ := runCI_sound_typed 12 instance_.store before valid
    (show runC (stepI neverFail) 12 instance_.store before = (instance_.store, waiting, toCallout.2.2) from
      by with_unfolding_all rfl)
  exact ⟨_, by simpa only [Reach, internalP_profile] using run, typing⟩

private def resumed (reply : Answer request.signature) : Thread := resumeResult instance_.store waiting reply.toResult

private theorem after_typed {results} (typedWaiting : ThreadOk instance_.store waiting results)
    (reply : Answer request.signature) (allowed : Answer.ThrowsBelow 0 reply) :
    ThreadOk instance_.store (resumed reply) results := by
  apply ScalarInstance.resume_answer_typed (profile neverFail) registered.ready.ok typedWaiting callout decode reply
  change Answer.ThrowsBelow instance_.store.exns.length reply
  simpa only [show instance_.store.exns.length = 0 from rfl] using allowed

private def suffix (reply : Answer request.signature) := runC (stepI neverFail) 12 instance_.store (resumed reply)

private theorem suffix_reaches {results} {reply : Answer request.signature}
    (valid : ThreadOk instance_.store (resumed reply) results) :
    Reach (profile neverFail) (instance_.store, resumed reply) ((suffix reply).1, (suffix reply).2.1) := by
  have eq : runC (stepI neverFail) 12 instance_.store (resumed reply) =
      ((suffix reply).1, (suffix reply).2.1, (suffix reply).2.2) := by simp only [Prod.eta, suffix]
  simpa only [Reach, internalP_profile] using (runCI_sound_typed 12 instance_.store (resumed reply) valid eq).1

/-- The actual erased wrapper realizes this tree on every reply admitted at its
empty exception store. Success continues to the numeric instruction; trap does not. -/
theorem wrapper_realizes : Realizes (profile neverFail) 0 op tree instance_.store before := by
  obtain ⟨_, run, valid⟩ := prefix_reaches_typed
  apply Realizes.ask run callout decode
  intro reply allowed
  have reaches := suffix_reaches (after_typed valid reply allowed)
  cases reply with
  | values value =>
    have same : value = (⟨[], .nil⟩ : Typed request.signature.results) :=
      Subtype.ext (List.forall₂_nil_left_iff.mp value.property)
    subst value
    exact .done reaches (by with_unfolding_all rfl)
  | trap => exact .done reaches (by with_unfolding_all rfl)
  | throw address => exact (Nat.not_lt_zero address allowed).elim

/-- Both directions for the complete, open round, without fixing a handler. -/
theorem wrapper_round_iff {moves : List (Move instance_.E instance_.F)}
    (legal : instance_.PlayThrowsBelow 0 moves) :
    Completes 0 op tree moves ↔ ∃ target, entry.round (profile neverFail) exportArgs moves target :=
  completes_iff_entry_round entry exportArgs wrapper_realizes legal

example : ∃ target, entry.round (profile neverFail) exportArgs
    [.inl (.ask (request.question callbackArgs)), .inl (.ans (request.question callbackArgs) emptyReply),
      .inr (.ans op success)] target :=
  wrapper_realizes.path_of_completes (.ask emptyReply trivial (.done success))

example : ∃ target, entry.round (profile neverFail) exportArgs
    [.inl (.ask (request.question callbackArgs)), .inl (.ans (request.question callbackArgs) .trap),
      .inr (.ans op .trap)] target :=
  wrapper_realizes.path_of_completes (.ask .trap trivial (.done .trap))

example : tree.handle (Env.silent instance_.E) = none := rfl
example : tree.handle (fun _ => some .trap) = some .trap := rfl

private theorem silent_diverges : Behaviour.diverges ∈
    entry.denote (profile neverFail) (Env.silent instance_.E) exportArgs :=
  handled_mem_entry entry exportArgs wrapper_realizes registered.ready.ok _
    (throwsBelow_silent _ _) (throwsBelow_silent _ _)

private def trapping : Env instance_.E := fun _ => some .trap

private theorem trapping_throws_below (n : Nat) : ThrowsBelow trapping n := by
  intro _ reply selected
  cases (Option.some.inj selected : .trap = reply)
  trivial

private theorem host_traps : Behaviour.traps ∈ entry.denote (profile neverFail) trapping exportArgs :=
  handled_mem_entry entry exportArgs wrapper_realizes registered.ready.ok trapping
    (trapping_throws_below _) (trapping_throws_below _)

end Silmaril.Wasm.Game.Intrinsic.Requests.Examples
