module

public import Silmaril.Wasm.Cfg.FunctionCfg.Defs
public import Silmaril.Proofs.Wasm.Cfg.CallGuard
public import Silmaril.Proofs.Wasm.Cfg.CallTransport
public import Silmaril.Proofs.Wasm.Cfg.TailTyped
public import Silmaril.Proofs.Wasm.Cfg.FunctionCfg

@[expose] public section

/-!
# The typed closed extended oracle on the `tExt`-checked fragment: completeness instances

For the region-level completeness theorems with `CX closedCallX` and the diverging callees
`calleeDivX o`, at the deterministic profile `profile o` and with no host:

* `callCompleteG_cx`: every Core run of a call on the fragment (`XCallOk`: a typed store of Wasm
  functions with function types, `tExt`-checked, and a typed invocation) to a result, from any
  caller frame and with any annotation, is answered by `CX closedCallX` with that result
  (`call_transport`, then `XProgress.invoke_closedX_adequacy`);
* `divCallComplete_cx`: a diverging call on the fragment is one `calleeDivX o` names
  (`div_call_transport`);
* `guardedCalls_cx`, `tailGuarded_cx`: from a typed start on a `tExt`-checked store of Wasm
  functions, every call and every pending tail call a host-free run reaches is on the fragment
  (typing is preserved; the store's functions are unchanged).
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Cfg.Function
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Abstract.XRecursion (closedCallX)

variable {H : Type}

/-- **Calls on the `tExt`-checked fragment**: a typed store of Wasm functions with function types,
`tExt`-checked, and a typed invocation. -/
def XCallOk (s : Store H) (a : Nat) (us : List Val) : Prop :=
  StoreOk s ∧ WasmFuncsT s ∧ StoreChkE tExt s.funcs ∧ InvokeOk s a us

theorem wasmFuncs_of_T {s : Store H} (hW : WasmFuncsT s) : WasmFuncs s := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  obtain ⟨fn, -, -, hcode, -⟩ := hW i _ (List.getElem?_eq_getElem hi)
  exact ⟨fn, hcode⟩

theorem result_vals {r : Result} {vs : List Val} (h : r.toAdmin = vals vs) : r = .values vs := by
  cases r with
  | values ws => simp only [Result.toAdmin] at h; rw [Sim.vals_injective h]
  | trap =>
    simp only [Result.toAdmin] at h
    exact absurd h.symm Proofs.Region.vals_ne_trap
  | throw t =>
    simp only [Result.toAdmin] at h
    have : Admin.plain .throwRef ∈ vals vs := by rw [← h]; simp
    obtain ⟨v, -, hv⟩ := List.mem_map.1 this
    have := congrArg Admin.val? hv
    rw [Admin.val?_toAdmin] at this
    simp [Admin.val?] at this

theorem result_trap {r : Result} (h : r.toAdmin = [.trap]) : r = .trap := by
  cases r with
  | values ws => simp only [Result.toAdmin] at h; exact absurd h Proofs.Region.vals_ne_trap
  | trap => rfl
  | throw t => simp [Result.toAdmin] at h

/-- **The typed closed extended oracle is complete on the `tExt`-checked fragment.** -/
theorem callCompleteG_cx (o : SingleThreaded.GrowOracle) :
    CallCompleteG (SingleThreaded.profile o) noHostX XCallOk
      (CX (closedCallX : Abstract.CallRel H)) := by
  intro s s' f f' a fi ps rs us c r hG hc hfi hty hn hrun
  obtain ⟨hs, hW, hS, hok⟩ := hG
  have he := expand_of_funcType hty
  obtain ⟨hf, hg⟩ := (call_transport hrun ⟨r, rfl⟩ (wasmFuncs_of_T hW)).2 us a c fi _ _ rfl hc hfi
    he (by simp [Ty.length_ofList, hn])
  refine ⟨hf, ?_⟩
  have hinv : Steps (SingleThreaded.profile o) noHostX (invoke s a us) ⟨s', {}, r.toAdmin⟩ := by
    have h2 := hg {} (.callRefType fi.type) trivial
    simpa [invoke, hfi] using h2
  obtain ⟨-, s₂, fl, hcl, hc'⟩ := (XProgress.invoke_closedX_adequacy (o := o) hs hok hS hW hfi
    hty).2.1 _ hinv (fun _ h => Step.result_stuck r h)
  have hE := entry_of_invokeOk (P := SingleThreaded.profile o) hs hok
  rcases hc' with ⟨ws, hws, he'⟩ | ⟨rfl, he'⟩
  · simp only [Config.mk.injEq] at he'
    obtain ⟨rfl, -, hv⟩ := he'
    obtain rfl := result_vals hv
    exact ⟨fl, ⟨hE, hcl⟩, ws, hws, rfl⟩
  · simp only [Config.mk.injEq] at he'
    obtain ⟨rfl, -, hv⟩ := he'
    obtain rfl := result_trap hv
    exact ⟨.trap, ⟨hE, hcl⟩, rfl⟩

/-- **`calleeDivX` is complete on the `tExt`-checked fragment.** -/
theorem divCallComplete_cx (o : SingleThreaded.GrowOracle) :
    DivCallComplete (SingleThreaded.profile o) noHostX XCallOk (calleeDivX (H := H) o) := by
  intro s f a fi ps rs us c hG hc hfi hty hn hdiv
  obtain ⟨hs, hW, hS, hok⟩ := hG
  have h' := div_call_transport (wasmFuncs_of_T hW) hc hfi (expand_of_funcType hty)
    (by simp [Ty.length_ofList, hn]) hdiv {} (cr' := .callRefType fi.type) trivial
  exact ⟨hs, hok, hS, hW, by simpa [invoke, hfi] using h'⟩

theorem wasmFuncsT_of_funcs {s s' : Store H} (h : s'.funcs = s.funcs) (hW : WasmFuncsT s) :
    WasmFuncsT s' := fun a fi hfi => hW a fi (h ▸ hfi)

/-- **The fragment's guard at every call, from a typed start.** -/
theorem guardedCalls_cx {P : Profile} {c₀ : Config H} (hT : Sim.ContextTyped c₀)
    (hW : WasmFuncsT c₀.store) (hS : StoreChkE tExt c₀.store.funcs) :
    GuardedCalls P (fun _ _ _ _ => False) XCallOk c₀ := by
  intro c₂ E ws us a cr rest fi ps rs h hc hcr hd hfi he hn
  have hfun := steps_funcs_closed h
  have hT₂ := hT.steps h
  obtain ⟨C, ts, xs, hs, -, -, -⟩ := hT₂.fragment_ctx
  refine ⟨hs, wasmFuncsT_of_funcs hfun hW, hfun ▸ hS, ?_⟩
  obtain ⟨s₂, f₂, code₂⟩ := c₂
  simp only at hc hfi ⊢
  subst hc
  exact invokeOk_of_typed (contextTyped_fill E hT₂) hcr hd hfi he hn

open Silmaril.Wasm.Execution.Core.PC in
/-- **A typed pending tail call types its arguments**: a typed `return_call_ref` form of `fi` on
its `ps.length` top values `args` is a typed invocation. -/
theorem invokeOk_of_retTyped {s : Store H} {f : Frame} {W₀ args : List Val} {a : Nat}
    {c : Admin} {fi : FuncInst H} {ps rs : Ty (.list .val)} {rest : List Admin}
    (h : Sim.ContextTyped ⟨s, f, vals W₀ ++ vals args ++ .ref (.func a) :: c :: rest⟩)
    (hcr : c.IsReturnCallRef) (hfi : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : args.length = ps.length) : InvokeOk s a args := by
  have h1 : Sim.ContextTyped ⟨s, f, vals W₀ ++ vals args ++ [.ref (.func a), c]⟩ :=
    Sim.ContextTyped.suffix (rest := rest) (by simpa using h)
  obtain ⟨C, ts, xs, hs, hC, hc, hcode⟩ := h1.fragment_ctx
  obtain ⟨_, xs₁, _, hp, h₂, _⟩ := AdminsOk.split hcode hC (vals W₀)
    (vals args ++ [.ref (.func a), c]) (by simp) (by simp)
  have hC' := hC.initLocals xs₁
  have hc' := hc.initLocals hp.vals_inits
  have hΔ := CtxOk.typesOk' hc'
  have hcd : ∀ d, c = .returnCallRefType d → TyOk {} d := by
    intro d hd
    have e0 : vals (args ++ [.ref (.func a)]) ++ [c] = vals args ++ [.ref (.func a), c] := by
      simp [vals, Val.toAdmin]
    have h' := h₂
    rw [← e0] at h'
    obtain ⟨tvs, it₀, M, T, hc0, -⟩ := redex_rep hC' (returnCallRef_inits hcr) h'
    obtain ⟨d₀, -, -, -, -, -, -, -, -, -, -, -, h3⟩ := inv_returnCallRef hcr hc0
    obtain ⟨rfl, hok⟩ := h3 d hd
    exact hok
  exact ⟨fi, ps, rs, hfi, he, Interp.retRef_args hs hC' hΔ hcr hcd hfi he hn h₂⟩

/-- **The fragment's guard at every pending tail call, from a typed start.** -/
theorem tailGuarded_cx {P : Profile} {c₀ : Config H} (hT : Sim.ContextTyped c₀)
    (hW : WasmFuncsT c₀.store) (hS : StoreChkE tExt c₀.store.funcs) :
    TailGuarded P (fun _ _ _ _ => False) XCallOk c₀ := by
  intro c₂ W₀ args a c rest fi ps rs h hc hcr hfi he hn
  have hfun := steps_funcs_closed h
  have hT₂ := hT.steps h
  obtain ⟨C, ts, xs, hs, -, -, -⟩ := hT₂.fragment_ctx
  refine ⟨hs, wasmFuncsT_of_funcs hfun hW, hfun ▸ hS, ?_⟩
  obtain ⟨s₂, f₂, code₂⟩ := c₂
  simp only at hc hfi ⊢
  subst hc
  exact invokeOk_of_retTyped hT₂ hcr hfi he hn

end Silmaril.Wasm.Cfg.Proofs.Region
