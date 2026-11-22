module

public import Silmaril.Wasm.Component.Reference.DirectLift.Defs
import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.RefSess
import Silmaril.Wasm.Game.Adequacy.Thms
import Silmaril.Wasm.Game.Machine.Thms

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.DirectLift

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Reference
  Silmaril.Wasm.Component.Reference.DirectLift Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Game Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {I : ScalarInstance} {shared : Store (CanonHost (core3P P))}
  {x : SimpleExport} {args : List Silmaril.Wasm.Component.Val} {question : I.F.Op}

private theorem host_eq (abi : Boundary I shared x args question) :
    hostOf I.imports (Env.silent I.E) = Det.noHost :=
  Silmaril.Proofs.Wasm.Component.Reference.hostOf_nil abi.noImports _

private theorem segment (abi : Boundary I shared x args question) {y : CoreSt (E3 P)}
    (run : Relation.ReflTransGen (CoreStep (E3 P))
      (shared, Thread.invokeFlat (I.addr question.1) (lowerArgs x.ty.params args)) y) :
    Reach P (Store.mapH (fun _ => 0) shared, I.initThread question)
      (Store.mapH (fun _ => 0) y.1, y.2) := by
  rw [ScalarInstance.initThread, abi.arguments]
  exact reach_mapH (fun _ => 0) (coreSteps_internal run)

private theorem answerAt (abi : Boundary I shared x args question) {y : CoreSt (E3 P)}
    (run : Relation.ReflTransGen (CoreStep (E3 P))
      (shared, Thread.invokeFlat (I.addr question.1) (lowerArgs x.ty.params args)) y)
    {result : Result} (final : (y.2.config y.1).code = result.toAdmin) :
    ∃ answer : I.F.Ar question,
      Answer.ofResult? (I.exports.get question.1) result = some answer ∧
      Entry.Finishes P Det.noHost
        (invoke (Store.mapH (fun _ => 0) shared) (I.addr question.1) question.2.val)
        (y.2.config (Store.mapH (fun _ => 0) y.1)) result ∧
      I.Activation P (Store.mapH (fun _ => 0) shared)
        [.inr (.ask question), .inr (.ans question answer)] (Store.mapH (fun _ => 0) y.1) := by
  have actual := segment abi run
  have code : ResultAt (Store.mapH (fun _ => 0) y.1) y.2 result :=
    (config_code_mapH _ _ _).trans final
  obtain ⟨answer, read, _⟩ := ScalarInstance.answer_of_run (f := question) abi.wellFormed
    (throwsBelow_silent I _) actual.steps code
  exact ⟨answer, read, ⟨actual.steps, code⟩,
    .cons (.call _ _) (.cons (.oret actual code read) (.nil _))⟩

private theorem noCallout (abi : Boundary I shared x args question) {y : CoreSt (E3 P)}
    (run : Relation.ReflTransGen (CoreStep (E3 P))
      (shared, Thread.invokeFlat (I.addr question.1) (lowerArgs x.ty.params args)) y)
    {code : CanonHost (E3 P)} {values : List FlatValue}
    (status : (core3P P).status y.1 y.2 = .callout code values) : False := by
  obtain ⟨_, _, _, _, redex⟩ := status_callout status
  obtain ⟨_, mapped⟩ := decompose?_mapH (fun _ => (0 : Nat)) redex
  rw [← config_code_mapH (fun _ => (0 : Nat)) y.1 y.2] at mapped
  rcases ScalarInstance.progress_hostOf (f := question) abi.wellFormed (throwsBelow_silent I _)
    (segment abi run).steps with ⟨result, finished⟩ | ⟨_, step⟩
  · rw [finished, Silmaril.Wasm.Binaryen.LinkBehaviours.decompose?_result] at mapped
    cases mapped
  · rw [host_eq abi] at step
    have absent := decompose?_none_of_noRedex (Step.noRedex step)
    dsimp only at absent
    have sameStore := Thread.config_store (Store.mapH (fun _ => (0 : Nat)) y.1) y.2
    rw [sameStore] at absent
    rw [absent] at mapped
    cases mapped

theorem terminalReadback {prof : ProfileKind} {ι : InstState} {garbage : Garb P} {call : Nat}
    {funcs : List (CFuncInst (core3P P))} {exports : List (String × FuncId)}
    {final : Machine.Config (core3P P) Unit} {out : CallOutcome}
    (abi : Boundary I shared x args question) (threads : ThreadsOk ι) (fresh : garbage.Fresh call)
    (named : ∃ func, exports.lookup x.name = some func ∧
      funcs[func.idx]? = some (.lifted (I.addr question.1) (liftedFt x) {} ⟨0⟩) ∧
      Calls prof (refHost P).hr (D P) (readyCfg shared ι funcs garbage) ⟨call⟩ func
        (args.map toRefVal) final out) :
    ∃ (core : Execution.Core.Config Nat) (result : Result) (answer : I.F.Ar question),
      Entry.Finishes P Det.noHost
        (invoke (Store.mapH (fun _ => 0) shared) (I.addr question.1) question.2.val) core result ∧
      answer.toResult = result ∧ Reports x out result ∧
      core.store = Store.mapH (fun _ => 0) final.store.core ∧
      I.Activation P (Store.mapH (fun _ => 0) shared)
        [.inr (.ask question), .inr (.ans question answer)] core.store := by
  obtain ⟨⟨func⟩, _, lifted, trace, steps, host, _, holds⟩ := named
  obtain ⟨_, invokeStep, afterInvoke⟩ := Steps.cons_iff.mp steps
  have afterInvoke := invoke_inv_k invokeStep ▸ afterInvoke
  obtain ⟨running, thread, cont, segs, rest, _, startRun, atCore⟩ :=
    SessionAdequacy.call_at_kT prof shared ι _ funcs garbage call func _ x args abi.floatFreeParams abi.typed
      abi.flatParams abi.oneResult abi.flatResults abi.floatFreeResults
      (addThread?_ok threads _) (removeThread?_enter _ _) lifted
  rcases startRun.inv afterInvoke with live | ⟨_, splitPrefix, restRun⟩
  · exact absurd holds (live.not_holds _ _)
  rcases coreCfg_steps_inv (core_run_k atCore.ctl atCore.core restRun) with
    ⟨y, _, same, _⟩ | ⟨y, _, _, _, tail, run, _, splitCore, exit, suffix⟩
  · have live : Live (coreCfg running thread cont segs rest y) := ⟨List.cons_ne_nil _ _, atCore.lock⟩
    exact absurd (same ▸ holds) (live.not_holds _ _)
  have tailHost : ∀ ev, Label.host ev ∈ tail → CallHostEvent ⟨call⟩ ev := by
    intro ev mem
    apply host ev
    rw [splitPrefix, splitCore]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
  have finish (result : Result) (code : (y.2.config y.1).code = result.toAdmin)
      (reported : Reports x out result) (store : final.store.core = y.1) :
      ∃ (core : Execution.Core.Config Nat) (result : Result) (answer : I.F.Ar question),
        Entry.Finishes P Det.noHost
          (invoke (Store.mapH (fun _ => 0) shared) (I.addr question.1) question.2.val) core result ∧
        answer.toResult = result ∧ Reports x out result ∧
        core.store = Store.mapH (fun _ => 0) final.store.core ∧
        I.Activation P (Store.mapH (fun _ => 0) shared)
          [.inr (.ask question), .inr (.ans question answer)] core.store := by
    obtain ⟨answer, read, finished, activation⟩ := answerAt abi run code
    exact ⟨_, result, answer, finished, Answer.toResult_of_ofResult? read, reported,
      by rw [Thread.config_store (Store.mapH (fun _ => (0 : Nat)) y.1) y.2, store],
      by simpa only [Thread.config_store (Store.mapH (fun _ => (0 : Nat)) y.1) y.2] using activation⟩
  rcases exit with ⟨ys, status, _, rfl⟩ | ⟨status, _, rfl⟩ | ⟨_, _, status⟩
  · obtain ⟨values, code, flat⟩ := status_values status
    obtain ⟨_, read, _, _⟩ := answerAt abi run (result := .values values) code
    have typed : List.Forall₂ ScalarType.HasVal (I.exports.get question.1).results values := by
      unfold Answer.ofResult? at read
      dsimp only at read
      split_ifs at read with valid
      exact valid
    rw [abi.signature] at typed
    have types := toFlat?_types _ _ _ typed flat
    cases lift : liftArgs x.ty.results ys with
    | some ws =>
      have result := result?_next fresh x func (I.addr question.1) (args.map toRefVal)
        (ws.map toRefVal) y.1 (InstState.removeThread 1 (enterInst ι ⟨garbage.threads.length⟩)) funcs
      obtain ⟨rfl, rfl⟩ := out_of_resolvesK (atCore.ret y ys ws types lift) result suffix tailHost holds
      exact finish (.values values) code ⟨ys, ws, flat, lift, rfl⟩ rfl
    | none =>
      obtain ⟨middle, reached, finalEq⟩ := SessionAdequacy.trapsNextT_inv (atCore.trapT y ys types lift) suffix holds
      have trap := out_of_trapsNextK (atCore.trap y ys types lift) suffix holds
      subst out
      exact finish (.values values) code ⟨ys, flat, lift⟩
        (finalEq ▸ congrArg (fun store => store.core) reached)
  · have same := steps_of_locked rfl rfl suffix
    subst final
    have hout : out = .trap := by
      cases out with
      | resolved _ => exact absurd holds.2.1 (by simp)
      | trap => rfl
      | deadlock => exact absurd holds.1.2.1 (by simp)
    subst out
    rcases status_trap status with trap | ⟨exn, thrown⟩
    · exact finish .trap trap trivial rfl
    · exact finish (.throw exn) thrown trivial rfl
  · exact (noCallout abi run status).elim

end Silmaril.Proofs.Wasm.Component.Reference.DirectLift
