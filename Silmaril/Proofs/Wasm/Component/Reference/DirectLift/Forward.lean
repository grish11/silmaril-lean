module

public import Silmaril.Wasm.Component.Reference.DirectLift.Init.Defs
import Silmaril.Proofs.Wasm.Component.Reference.DirectLift.Init
import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.RefSess
import Silmaril.Wasm.Game.Adequacy.Thms
import Silmaril.Wasm.Game.Machine.Thms

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.DirectLift

open Silmaril.Proofs.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Reference
  Silmaril.Wasm.Component.Reference.DirectLift Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {I : ScalarInstance} {shared : Store (CanonHost (core3P P))}
  {x : SimpleExport} {args : List Silmaril.Wasm.Component.Val} {question : I.F.Op}

private theorem forwardAt {prof : ProfileKind} {ι : InstState} {garbage : Garb P} {call func : Nat}
    {funcs : List (CFuncInst (core3P P))} {core : Execution.Core.Config Nat} {result : Result}
    (abi : Boundary I shared x args question) (threads : ThreadsOk ι) (fresh : garbage.Fresh call)
    (lifted : funcs[func]? = some (.lifted (I.addr question.1) (liftedFt x) {} ⟨0⟩))
    (run : Entry.Finishes P Det.noHost
      (invoke (Store.mapH (fun _ => 0) shared) (I.addr question.1) question.2.val) core result) :
    ∃ final out, Calls prof (refHost P).hr (D P) (readyCfg shared ι funcs garbage) ⟨call⟩ ⟨func⟩
      (args.map toRefVal) final out ∧ Reports x out result ∧
      final.store.core = Store.mapH (someHost P) core.store := by
  have entrySteps : Execution.Core.Steps P Det.noHost
      ((Thread.invokeFlat (I.addr question.1) (lowerArgs x.ty.params args)).config
        (Store.mapH (fun _ => 0) shared)) core := by
    change Execution.Core.Steps P Det.noHost (invoke (Store.mapH (fun _ => 0) shared)
      (I.addr question.1) ((lowerArgs x.ty.params args).map ofFlat)) core
    rw [← abi.arguments]
    exact run.1
  obtain ⟨store, terminal, reach, endpoint⟩ := Reach.of_steps entrySteps
  have endStore : store = core.store := (Thread.config_store store terminal).symm.trans
    (congrArg Execution.Core.Config.store endpoint)
  subst store
  have remap : Store.mapH (someHost P) (Store.mapH (fun _ => (0 : Nat)) shared) = shared :=
    mapH_mapH_of_noHostFns _ _ (noHostFns_of_mapH (noHostFns_of_wf abi.noImports abi.wellFormed))
  have coreRun := coreSteps_of_reach (someHost P) reach
  rw [remap] at coreRun
  obtain ⟨running, thread, cont, segs, rest, startLabels, startRun, atCore⟩ :=
    SessionAdequacy.call_at_kT prof shared ι _ funcs garbage call func _ x args abi.floatFreeParams abi.typed
      abi.flatParams abi.oneResult abi.flatResults abi.floatFreeResults
      (addThread?_ok threads _) (removeThread?_enter _ _) lifted
  obtain ⟨middle, coreLabels, corePath⟩ := coreCfg_steps_of (prof := prof) (hr := (refHost P).hr)
    (dispatch := D P) (B := running) (th := thread) (K := cont) (segs := segs) (rest := rest) coreRun
  have startLive : Live running := ⟨by rw [atCore.ctl]; exact List.cons_ne_nil _ _, atCore.lock⟩
  have first : Step prof (refHost P).hr (D P) (readyCfg shared ι funcs garbage)
      (.host (.invoke ⟨call⟩ ⟨func⟩ (args.map toRefVal)))
      (invokedAt shared ι funcs garbage call func (args.map toRefVal)) := by
    refine Step.hostInvoke ⟨rfl, rfl, rfl⟩ fun pending mem same => ?_
    have smaller := fresh.pending pending mem
    rw [same] at smaller
    exact Nat.lt_irrefl call smaller
  let finishStore := Store.mapH (someHost P) core.store
  let reached := coreCfg running thread cont segs rest (finishStore, terminal)
  have activePath : Machine.Steps prof (refHost P).hr (D P) running middle reached :=
    eq_core_k atCore.ctl atCore.core ▸ corePath
  have path : Machine.Steps prof (refHost P).hr (D P) (readyCfg shared ι funcs garbage)
      (.host (.invoke ⟨call⟩ ⟨func⟩ (args.map toRefVal)) :: (startLabels ++ middle)) reached :=
    .cons first (steps_append startRun.steps activePath)
  have complete {tailLabels : List (Label (E3 P) Unit)} {final : Machine.Config (core3P P) Unit}
      {out : CallOutcome} (after : Machine.Steps prof (refHost P).hr (D P) reached tailLabels final)
      (noHost : ∀ ev, Label.host ev ∉ tailLabels)
      (noInternal : out = .trap → ∀ msg, Label.trap (.internal msg) ∉ tailLabels)
      (holds : out.Holds (refHost P).hr ⟨call⟩ final) :
      Calls prof (refHost P).hr (D P) (readyCfg shared ι funcs garbage) ⟨call⟩ ⟨func⟩
        (args.map toRefVal) final out := by
    refine ⟨(startLabels ++ middle) ++ tailLabels, ?_, ?_, ?_, holds⟩
    · simpa only [List.cons_append] using steps_append path after
    · intro ev mem
      rcases List.mem_append.mp mem with mem | mem
      · rcases List.mem_append.mp mem with mem | mem
        · exact (Adequacy.LRun.no_host startRun ev mem).elim
        · exact (not_host_of_core coreLabels ev mem).elim
      · exact (noHost ev mem).elim
    · intro isTrap msg mem
      rcases List.mem_append.mp mem with mem | mem
      · rcases List.mem_append.mp mem with mem | mem
        · exact Adequacy.LRun.no_trap startRun startLive _ mem
        · exact not_trap_of_core coreLabels _ mem
      · exact noInternal isTrap msg mem
  have code : (terminal.config finishStore).code = result.toAdmin :=
    (config_code_mapH' _ _ _).trans ((congrArg Execution.Core.Config.code endpoint).trans run.2)
  have trapCase (status : (E3 P).status finishStore terminal = .returned .trap)
      (reports : Reports x .trap result) :
      ∃ final out, Calls prof (refHost P).hr (D P) (readyCfg shared ι funcs garbage) ⟨call⟩ ⟨func⟩
        (args.map toRefVal) final out ∧ Reports x out result ∧ final.store.core = finishStore := by
    refine ⟨trapCfg reached, .trap, complete (.cons (Step.coreTrap rfl status) (.refl _))
      (by intro ev; simp) (by intro _ msg; simp) (trapCfg_lockdown _), reports, rfl⟩
  cases result with
  | trap =>
    apply trapCase _ trivial
    change flatStatus (statusP P _ _) = _
    rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_trap code]
    rfl
  | throw exn =>
    apply trapCase _ trivial
    change flatStatus (statusP P _ _) = _
    rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_throwing code]
    rfl
  | values values =>
    have hostEq : hostOf I.imports (Env.silent I.E) = Det.noHost :=
      Silmaril.Proofs.Wasm.Component.Reference.hostOf_nil abi.noImports _
    obtain ⟨_, read, _⟩ := ScalarInstance.answer_of_run (f := question) abi.wellFormed
      (throwsBelow_silent I _) (hostEq ▸ run.1) run.2
    have typed : List.Forall₂ ScalarType.HasVal (I.exports.get question.1).results values := by
      unfold Answer.ofResult? at read
      dsimp only at read
      split_ifs at read with valid
      exact valid
    rw [abi.signature] at typed
    obtain ⟨flats, flat⟩ := Silmaril.Proofs.Wasm.Component.Core3G.toFlat?_isSome typed
    have types := toFlat?_types _ _ _ typed flat
    have status : (E3 P).status finishStore terminal = .returned (.values flats) := by
      change flatStatus (statusP P _ _) = _
      rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_values code]
      simp only [flatStatus, flat]
    have returned : Step prof (refHost P).hr (D P) reached .tau
        (retCfg running thread cont segs rest (finishStore, terminal) flats) :=
      Step.coreReturned rfl status
    cases lift : liftArgs x.ty.results flats with
    | some values =>
      obtain ⟨_, _, tailRun, rfl⟩ := atCore.ret (finishStore, terminal) flats values types lift
      refine ⟨_, .resolved (some (values.map toRefVal)), complete (.cons returned tailRun.steps)
        ?_ (fun impossible => nomatch impossible) ⟨rfl, rfl, result?_next fresh x func _ _ _ _ _ _⟩,
        ⟨flats, values, flat, lift, rfl⟩, rfl⟩
      · intro ev mem
        exact Adequacy.LRun.no_host tailRun ev ((List.mem_cons.mp mem).resolve_left (by simp))
    | none =>
      obtain ⟨trapped, reason, specTrap, tailRun, sameStore, _, trapStep⟩ :=
        atCore.trapT (finishStore, terminal) flats types lift
      refine ⟨trapCfg trapped, .trap, complete
        (.cons returned (steps_append tailRun.steps (.cons trapStep.1 (.refl _))))
        (by intro ev; simp) (by intro _ msg; simp [Ne.symm (specTrap msg)]) (trapCfg_lockdown _),
        ⟨flats, flat, lift⟩, ?_⟩
      exact congrArg (fun st => st.core) sameStore

theorem terminalForwardOfInstantiation {w : DirectWire} {prof : ProfileKind}
    {cfg : Machine.Config (core3P P) Unit} {owner : InstId} {exports : List (String × FuncId)}
    {func : FuncId} {call : Nat} {core : Execution.Core.Config Nat} {result : Result}
    (data : w.Prepared P shared (I.addr question.1)) (abi : Boundary I shared x args question)
    (signature : w.liftType = liftedFt x)
    (init : Instantiates prof (refHost P).hr (D P) (initConfig ()) w.component [] cfg owner exports)
    (named : exports.lookup x.name = some func)
    (run : Entry.Finishes P Det.noHost
      (invoke (Store.mapH (fun _ => 0) shared) (I.addr question.1) question.2.val) core result) :
    ∃ final out, Calls prof (refHost P).hr (D P) cfg ⟨call⟩ func (args.map toRefVal) final out ∧
      Reports x out result ∧ core.store = Store.mapH (fun _ => 0) final.store.core := by
  obtain ⟨rfl, rfl, rfl⟩ := (instantiates_iff data).mp init
  have funcEq : func = ⟨0⟩ := by
    simp only [DirectWire.exportMap, List.lookup_cons] at named
    split at named
    · exact (Option.some.inj named).symm
    · cases named
  subst func
  have fresh : Garb.Fresh (emptyGarb P) call := by
    constructor <;> intro item member <;> cases member
  obtain ⟨final, out, calls, reports, storeEq⟩ := forwardAt (prof := prof) (call := call)
    (ι := {}) (garbage := emptyGarb P) (func := 0)
    (funcs := [.lifted (I.addr question.1) w.liftType {} ⟨0⟩]) abi
    (.inl rfl) fresh (by rw [signature]; rfl) run
  have hostEq : hostOf I.imports (Env.silent I.E) = Det.noHost :=
    Silmaril.Proofs.Wasm.Component.Reference.hostOf_nil abi.noImports _
  have finalWF := (ScalarInstance.wellFormed_after_run (f := question) abi.wellFormed
    (throwsBelow_silent I _) (hostEq ▸ run.1) run.2).1
  exact ⟨final, out, calls, reports, by rw [storeEq, mapH_mapH_of_noHostFns _ _
    (noHostFns_of_wf abi.noImports finalWF)]⟩

private theorem report_unique {out other : CallOutcome} {result : Result}
    (first : Reports x out result) (second : Reports x other result) : out = other := by
  let observe : Result → Option CallOutcome
    | .trap | .throw _ => some .trap
    | .values values => (values.mapM toFlat?).map fun flats =>
      match liftArgs x.ty.results flats with
      | some values => .resolved (some (values.map toRefVal))
      | none => .trap
  have agrees {reported : CallOutcome} (report : Reports x reported result) :
      observe result = some reported := by
    cases reported with
    | resolved payload =>
      cases payload with
      | none => cases result <;> exact False.elim report
      | some payload =>
        cases result with
        | trap | throw _ => exact False.elim report
        | values values =>
          obtain ⟨flats, lifted, flat, lift, rfl⟩ := report
          simp [observe, flat, lift]
    | deadlock => cases result <;> exact False.elim report
    | trap =>
      cases result with
      | trap | throw _ => rfl
      | values values =>
        obtain ⟨flats, flat, rejects⟩ := report
        simp [observe, flat, rejects]
  exact Option.some.inj ((agrees first).symm.trans (agrees second))

theorem terminalObservationIff {w : DirectWire} {prof : ProfileKind}
    {cfg : Machine.Config (core3P P) Unit} {owner : InstId} {exports : List (String × FuncId)}
    {func : FuncId} {call : Nat} {out : CallOutcome} {store : Store Nat}
    (data : w.Prepared P shared (I.addr question.1)) (abi : Boundary I shared x args question)
    (signature : w.liftType = liftedFt x)
    (init : Instantiates prof (refHost P).hr (D P) (initConfig ()) w.component [] cfg owner exports)
    (named : exports.lookup x.name = some func) :
    (∃ final, Calls prof (refHost P).hr (D P) cfg ⟨call⟩ func (args.map toRefVal) final out ∧
      store = Store.mapH (fun _ => 0) final.store.core) ↔
    (∃ (core : Execution.Core.Config Nat) (result : Result),
      Entry.Finishes P Det.noHost
        (invoke (Store.mapH (fun _ => 0) shared) (I.addr question.1) question.2.val) core result ∧
      Reports x out result ∧ store = core.store) := by
  constructor
  · rintro ⟨final, ran, storeEq⟩
    obtain ⟨core, result, _, finished, _, reports, mapped, _⟩ :=
      terminalReadbackOfInstantiation data abi signature init named ran
    exact ⟨core, result, finished, reports, storeEq.trans mapped.symm⟩
  · rintro ⟨core, result, finished, reports, storeEq⟩
    obtain ⟨final, actual, ran, reported, mapped⟩ :=
      terminalForwardOfInstantiation data abi signature init named finished
    exact ⟨final, report_unique reports reported ▸ ran, storeEq.trans mapped⟩

end Silmaril.Proofs.Wasm.Component.Reference.DirectLift
