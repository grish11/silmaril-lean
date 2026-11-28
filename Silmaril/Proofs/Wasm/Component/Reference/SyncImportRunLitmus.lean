module

public import Silmaril.Wasm.Component.Reference.Litmus.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LitmusSeqI
import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.RefRun

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Litmus

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.Runtime hiding Thread
open Silmaril.Wasm.Execution.Core (ExternAddr Val vals)
open Silmaril.Wasm.SingleThreaded (Thread decompose? decompose?_top decompose?_vals_nil
  hostArity? neverFail profile resumeResult)

local notation "P₀" => profile neverFail
local notation "E₀" => core3P (profile neverFail)

private def ty := fwdS.imports[0].2
private noncomputable def lower : CanonHost E₀ := .lowered ⟨0⟩ (witFt ty) {} ⟨0⟩
private def thread := Thread.invokeFlat 0 [Flat.i32 3]

theorem fwd_reference_calls :
    let h := answerHostS P₀ fwdC
    ∃ ready finished exports f,
      Instantiates .deterministic h.hr h.dispatch
        (Config.init (hostFuncs 0 fwdS.imports CStore.empty) 10)
        fwdS.toRef (importArgs fwdS.imports) ready ⟨0⟩ exports ∧
      exports.lookup "f" = some f ∧
      Calls .deterministic h.hr h.dispatch ready ⟨0⟩ f [toRefVal (.u32 3)] finished
        (.resolved (some [toRefVal (.u32 13)])) ∧ finished.host = 11 := by
  let h := answerHostS P₀ fwdC
  obtain ⟨I, cs, ci, facts⟩ := coreFactsI (Pf := P₀) fwdS_good fwdS_inst
  have same : I = fwdInst := ImpModule.IsInst.unique facts.isInst fwd_isInst
  subst I
  obtain ⟨initTrace, quiet, obs, instRun⟩ :=
    instI_detRunL (prof := .deterministic) (hr := h.hr) (D := h.dispatch)
      fwdS_good fwdS_inst fwdS_arity facts 10
  let fs := fwdS.afterFuncs P₀ fun i => fwdInst.addrs.getD i 0
  let ready := afterInstH P₀ cs fs 10
  have initialized : Instantiates .deterministic h.hr h.dispatch
      (Config.init (hostFuncs 0 fwdS.imports CStore.empty) 10)
      fwdS.toRef (importArgs fwdS.imports) ready ⟨0⟩ (exportMapI fwdS) := by
    refine ⟨initTrace, .cons (.hostRun ⟨rfl, rfl, rfl⟩) instRun.toDetRun.steps, ?_, rfl, rfl, ?_⟩
    · intro ev mem
      rcases quiet _ mem with eq | ⟨_, eq⟩ <;> cases eq
    · rw [obs, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
  obtain ⟨M, th, k, segs, rest, pre, entryRun, atCore, host⟩ :=
    call_atA (g := fwdC) .deterministic cs fs 10 1 0 fwdS.exports[0] [.u32 3]
      rfl rfl (by decide) (by decide) (by decide) rfl
      (afterFuncs_lifted (c := fwdS) _ (j := 0) (by decide))
  have storeEq : cs = trampStore P₀ fwdS.imports := by
    have concrete : ∃ i, (E₀).prepare? (trampStore P₀ fwdS.imports) fwdS.mod.mod
        ((List.range fwdS.imports.length).map ExternAddr.func) =
          some (trampStore P₀ fwdS.imports, i, none) := ⟨_, rfl⟩
    obtain ⟨i, hi⟩ := concrete
    exact (Prod.mk.inj (Option.some.inj (facts.prepare.symm.trans hi))).1
  have decomp : decompose? cs (thread.config cs).code =
      some (.top [] [], 0, lower, [Val.i32 3]) := by
    rw [storeEq]
    let s := trampStore P₀ fwdS.imports
    change decompose? s
      (vals ([Val.i32 3] ++ [.ref (.func 0)]) ++
        [.callRefType ((s.funcs[0]?.map Silmaril.Wasm.Execution.Core.FuncInst.type).getD default)]) = _
    have arity : hostArity? s 0 = some (lower, 1) := rfl
    rw [decompose?_top (pre := [Val.i32 3]) (n := 1) (by rfl) arity (Nat.le_refl 1)]
    rfl
  have status : (E₀).status M.store.core thread = .callout lower [Flat.i32 3] := by
    rw [atCore.core]
    change flatStatus (Silmaril.Wasm.Game.statusP P₀ cs thread) = _
    have noValues : ¬ ∃ vs, (thread.config cs).code = vals vs := by
      rintro ⟨vs, eq⟩
      erw [eq, decompose?_vals_nil] at decomp
      cases decomp
    have noTrap : (thread.config cs).code ≠ [.trap] := by intro eq; cases eq
    have noThrow : ¬ ∃ a, (thread.config cs).code =
        Silmaril.Wasm.Execution.Core.throwing a := by
      rintro ⟨a, eq⟩
      cases eq
    simp only [Silmaril.Wasm.Game.statusP, noValues, noTrap, noThrow, dite_false, ite_false, decomp]
    rfl
  have active : M.ctl = ⟨th, .core thread k, segs⟩ :: rest := atCore.ctl
  let parked := { M with ctl := ⟨th, .prog (h.dispatch (.hostCallout lower [Flat.i32 3])),
    .core thread k :: segs⟩ :: rest }
  have park : Step .deterministic h.hr h.dispatch M .tau parked := .coreCallout active status
  obtain ⟨st, inst, leave⟩ := atCore.inst
  have binding : ArenaField.funcs.get? parked.store ⟨0⟩ = some (.host (witFt ty) ⟨0⟩) := by
    change M.store.funcs[0]? = _
    rw [atCore.funcs]
    rfl
  have reply : fwdC parked.host ⟨0⟩ [toRefVal (.u32 3)] =
      some ([toRefVal (.u32 13)], 11) := by
    change fwdC M.host _ _ = _
    rw [host]
    rfl
  obtain ⟨pos, tr, called⟩ := runs_callout (g := fwdC) (m := parked) (p := ty)
    (ys := [.i32 3]) (ws := [.u32 3]) (us := [.u32 13]) (atCore.entry _ _ _)
    inst leave binding rfl rfl (by decide) rfl reply (by decide) rfl rfl (by decide)
  have parkBind : parked.ctl = ⟨th, .prog (h.dispatch (.hostCallout lower [Flat.i32 3]) >>= Prog.pure),
      .core thread k :: segs⟩ :: rest := by
    rw [Prog.bind_eq, Prog.bind_pure]
  have serviced := called.lrun_at (prof := .deterministic) (hr := h.hr)
    atCore.lock Prog.pure parkBind
  let subtasks := [{ resolvedSub ⟨0⟩ [Flat.i32 13] with lenders := none }]
  let callers : List (Caller E₀) :=
    [lowerRec ⟨M.store.subtasks.length⟩ ⟨0⟩ [Flat.i32 3] ty pos]
  let base := extSC (withH M 11) subtasks callers
  let t' := (E₀).resume cs thread (.values [Flat.i32 13])
  let resolved := { parked with
    host := 11
    store := calloutSt parked.store ⟨0⟩ [Flat.i32 3] ty pos [Flat.i32 13]
    ctl := ⟨th, .prog (.pure (.flat [Flat.i32 13])), .core thread k :: segs⟩ :: rest }
  have pop : Step .deterministic h.hr h.dispatch resolved .tau
      (coreCfg base th k segs rest (cs, t')) := by
    dsimp only [resolved, base, t']
    rw [calloutSt_eq, ← atCore.core]
    exact .popCore rfl
  have returned : (E₀).status cs t' = .returned (.values [Flat.i32 13]) := by
    have code : (t'.config cs).code = vals [Val.i32 13] := by
      change (((E₀).resume cs thread (.values [Flat.i32 13])).config cs).code = _
      rw [resume_values]
      change ((resumeResult cs thread (.values [Val.i32 13])).config cs).code = _
      simp only [resumeResult, decomp]
      rfl
    change flatStatus (Silmaril.Wasm.Game.statusP P₀ cs t') = _
    have existsVals : ∃ vs, (t'.config cs).code = vals vs := ⟨_, code⟩
    simp only [Silmaril.Wasm.Game.statusP, dite_eq_left existsVals]
    rw [Silmaril.Wasm.SingleThreaded.vals_injective (existsVals.choose_spec.symm.trans code)]
    rfl
  have lift : Step .deterministic h.hr h.dispatch (coreCfg base th k segs rest (cs, t')) .tau
      (retCfg base th k segs rest (cs, t') [Flat.i32 13]) := .coreReturned rfl returned
  obtain ⟨post, finished, suffix, hctl, hlock, hresult, _, finishedHost, _⟩ :=
    atCore.ret 11 subtasks callers (cs, t') [Flat.i32 13] [.u32 13] rfl rfl
  have popLive : Live resolved := by
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    change (calloutSt parked.store ⟨0⟩ [Flat.i32 3] ty pos [Flat.i32 13]).lockdown = false
    rw [calloutSt_eq]
    exact atCore.lock
  have resumeRun : LRun .deterministic h.hr h.dispatch resolved (.tau :: .tau :: post) finished :=
    .cons popLive (.of_prog rfl (fun _ _ eq => by cases eq) pop)
      (.cons ⟨List.cons_ne_nil _ _, atCore.lock⟩
        (.of_core rfl (by
          change (E₀).status cs t' ≠ .running ∧ (E₀).status cs t' ≠ .stuck
          rw [returned]
          simp) lift) suffix)
  have fromCore : LRun .deterministic h.hr h.dispatch M (.tau :: (tr ++ .tau :: .tau :: post))
      finished :=
    .cons ⟨by rw [active]; exact List.cons_ne_nil _ _, atCore.lock⟩
      (.of_core active (by rw [status]; simp) park) (serviced.trans resumeRun)
  have called := entryRun.trans fromCore
  refine ⟨ready, finished, exportMapI fwdS, ⟨1⟩, initialized, rfl, ?_, finishedHost⟩
  exact ⟨_, .cons (.hostInvoke ⟨rfl, rfl, rfl⟩ (by simp [ready, afterInstH, Config.init])) called.steps,
    fun ev mem => (Adequacy.LRun.no_host called ev mem).elim, fun bad => CallOutcome.noConfusion bad,
    hctl, hlock, hresult⟩

end Silmaril.Proofs.Wasm.Component.Reference.Litmus
