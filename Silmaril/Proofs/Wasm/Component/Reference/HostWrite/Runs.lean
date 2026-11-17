module

public import Silmaril.Proofs.Wasm.Component.Reference.HostWrite.Step
public import Silmaril.Wasm.Component.Reference.LinkedSession.Defs
public import Silmaril.Wasm.Component.Reference.SessionAdequacy.Defs

/-!
# Host-state writes along machine runs: instantiation, calls and sessions

* `calls_cfgSafe`, `instantiates_cfgSafe`: top-level calls and root instantiation keep `CfgSafe`
  (the only host-frame program of an instantiation is `instantiateProg`, which never writes the
  host state: `nsProg_instantiateProg`);
* `calls_ctl`: a top-level call starts from a configuration with an empty control chain, so
  `cfgSafe_resumeCfg`: resuming after a trapped call (`resumeCfg`) keeps `CfgSafe`;
* `sessRun_cfgSafe`: resumable sessions keep `CfgSafe`;
* `hostChain_logExt`: along `logExt` steps the host state is unchanged or its log strictly grows.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HostWrite

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.Reference

variable {E : CoreEngine} {σ : Type} {Ext : σ → σ → Prop}
variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

theorem calls_cfgSafe (hd : DispatchSafe Ext dispatch) {m m' : Config E σ} {c : CallId}
    {f : FuncId} {args : List Silmaril.Wasm.Component.Reference.Val} {out : CallOutcome}
    (h : Calls prof hr dispatch m c f args m' out) (hm : CfgSafe Ext m) :
    CfgSafe Ext m' ∧ HostChain Ext m.host m'.host := by
  obtain ⟨tr, hs, hh, -, -⟩ := h
  refine steps_cfgSafe hd hs hm fun p hp => ?_
  rcases List.mem_cons.1 hp with e | hp'
  · cases e
  · rcases hh _ hp' with e | e <;> cases e

/-- A top-level call starts with the host in control: the control chain is empty. -/
theorem calls_ctl {m m' : Config E σ} {c : CallId} {f : FuncId}
    {args : List Silmaril.Wasm.Component.Reference.Val} {out : CallOutcome}
    (h : Calls prof hr dispatch m c f args m' out) : m.ctl = [] := by
  obtain ⟨tr, hs, -, -, -⟩ := h
  cases hs with
  | cons s _ =>
    cases s with
    | hostInvoke hrdy _ => exact hrdy.1

theorem cfgSafe_resumeCfg {m mT : Config E σ} (hm : CfgSafe Ext m) (hc : m.ctl = []) :
    CfgSafe Ext (Silmaril.Wasm.Component.Reference.resumeCfg m mT) := by
  refine ⟨?_, hm.2⟩
  show CtlSafe Ext _ m.ctl
  rw [hc]
  trivial

theorem instantiates_cfgSafe [∀ a b, Decidable (E.ExternSub a b)]
    (hd : DispatchSafe Ext dispatch) {c : Syntax.Component E.Module}
    {args : Instantiate.Exports E} {m m₀ : Config E σ} {inst : InstId}
    {es : List (String × FuncId)} (h : Instantiates prof hr dispatch m c args m₀ inst es)
    (hm : CfgSafe Ext m) : CfgSafe Ext m₀ ∧ HostChain Ext m.host m₀.host := by
  obtain ⟨tr, hs, hh, -⟩ := h
  refine steps_cfgSafe hd hs hm fun p hp' => ?_
  rcases List.mem_cons.1 hp' with e | hp''
  · cases e
    exact HostSafe.of_invW (nsProg_instantiateProg c args) none
  · exact absurd hp'' (hh _)

theorem sessRun_cfgSafe [∀ a b, Decidable (E.ExternSub a b)] {h : Host E σ}
    (hd : DispatchSafe Ext h.dispatch) {m m' : Config E σ} {k : Nat}
    {calls : List (FuncId × List Silmaril.Wasm.Component.Reference.Val)}
    {outs : List (Option (List Silmaril.Wasm.Component.Reference.Val))}
    (hr : LinkedSession.SessRun prof h m k calls outs m') (hm : CfgSafe Ext m) :
    CfgSafe Ext m' := by
  induction hr with
  | nil => exact hm
  | ret hc _ ih => exact ih (calls_cfgSafe hd hc hm).1
  | trap hc _ ih =>
    exact ih (cfgSafe_resumeCfg hm (calls_ctl hc))

/-- Along `logExt` steps the host state is unchanged, or its log strictly grows. -/
theorem hostChain_logExt {σ₀ ε : Type} {s s' : σ₀ × List ε} (h : HostChain logExt s s') :
    s' = s ∨ logExt s s' := by
  induction h with
  | refl => exact .inl rfl
  | tail _ hx ih =>
    rcases ih with rfl | ⟨hp, hl⟩
    · exact .inr hx
    · exact .inr ⟨hp.trans hx.1, hl.trans hx.2⟩

end Silmaril.Proofs.Wasm.Component.Reference.HostWrite
