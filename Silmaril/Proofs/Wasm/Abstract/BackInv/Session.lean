module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingS.Core
public import Silmaril.Wasm.Abstract.HostClosingS.Thms
public import Silmaril.Wasm.Abstract.HostClosingInfXPBack.Thms
public import Silmaril.Wasm.Abstract.HostSessionXP.Defs
public import Silmaril.Wasm.Abstract.NodeBridge.Defs

/-!
# Core behaviours are session behaviours, for every invariant (proofs)

For a `BackInv` `J`, a host in `J.HostOk` in the host slices, and an invocation in `J.CT` (on a
checked store with the tag invariants, typed arguments), at a deterministic profile `profile o`:

* `coreBehSXP_mem`: every finished Core behaviour (`CoreBehSXP`: values, uncaught exception,
  trap in its store, host-free divergence after a log) is one of the session closure with
  divergence (`wasmEvFunDXPS`);
* `coreCallout_mem`: every Core callout is a pending session call (`wasmEvPendXPS`);
* `coreInf_mem`: every productive Core run is a productive stream (`wasmEvInfNXP`).

Each is the backward simulation for `J` (`BackInv.evRun_wasmEvFunXP_vals`, …,
`BackInv.coreInf_wasmEvInfNXP`); a store-keeping trap is read off the trap of the closure by
determinism (`evRun_wasmEvFunXPS_trap'`, as `HostClosingS.evRun_wasmEvFunXPS_trap`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.BackInv

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Interp (BackInv HostSliceT HostSliceE TagsOk StoreChkE ehExt)
open Silmaril.Games.Abstract.StratSession (eraseEnd)
open Silmaril.Proofs.Wasm.Abstract.HostClosingS (close_lift eraseEnd_eq_trap close_ne_trap)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {H : Type} (J : BackInv H) {o : GrowOracle} {host : HostSemantics H}
  {tags : List TagInst} {s : Store H} {a : Nat} {vs : List Val}

/-- A Core run of an invocation in the invariant to a trap in `s₂` is the session trap in
`s₂`. -/
theorem evRun_wasmEvFunXPS_trap' (hT : J.HostOk host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) {s₂ : Store H} {cs : List (Call (wasmHostSig H))}
    (hct : J.CT (invoke s a vs)) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hok : InvokeOk s a vs) (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩) :
    (cs, .ret (.inr ()) s₂) ∈ wasmEvFunXPS s (a, vs) := by
  obtain ⟨⟨c', e'⟩, hy', hc', he'⟩ :=
    close_lift (J.evRun_wasmEvFunXP_trap hT hH hE hct hS hts hok hrun)
  obtain rfl : c' = cs := hc'
  rcases eraseEnd_eq_trap he' with rfl | ⟨s₂', rfl⟩
  · exact absurd hy' close_ne_trap
  · obtain ⟨rfl, -⟩ := evRun_trap_det
      (wasmEvFunXPS_trap_evRun (P := profile o) hH hE hts hS hok hy' (evRun_consistent hrun)) hrun
    exact hy'

/-- **Finished Core behaviours are session behaviours.** -/
theorem coreBehSXP_mem (hT : J.HostOk host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    (hct : J.CT (invoke s a vs)) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hok : InvokeOk s a vs) {y : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit)}
    (hy : CoreBehSXP (profile o) host s (a, vs) y) : y ∈ wasmEvFunDXPS s (a, vs) := by
  obtain ⟨cs, e⟩ := y
  rcases e with ⟨(ws | t) | u, s₂⟩ | _ | _
  · exact .inl (mem_wasmEvFunXPS_ret_iff.2 (J.evRun_wasmEvFunXP_vals hT hH hE hct hS hts hok hy))
  · exact .inl (mem_wasmEvFunXPS_ret_iff.2 (J.evRun_wasmEvFunXP_throw hT hH hE hct hS hts hok hy))
  · exact .inl (evRun_wasmEvFunXPS_trap' J hT hH hE hct hS hts hok hy)
  · exact hy.elim
  · obtain ⟨c', hrun, hd⟩ := hy
    exact .inr ⟨rfl, J.evRun_wasmEvFunDXP_div hT hH hE hct hS hts hok hrun hd⟩

/-- **Core callouts are pending session calls.** -/
theorem coreCallout_mem (hT : J.HostOk host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    (hct : J.CT (invoke s a vs)) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hok : InvokeOk s a vs) {x : List (Call (wasmHostSig H)) × (wasmHostSig H).Op}
    (hx : NodeBridge.CoreCallout (profile o) host s (a, vs) x) : x ∈ wasmEvPendXPS s (a, vs) := by
  obtain ⟨cs, hh, s', us⟩ := x
  obtain ⟨c, E, a', hrun, hd, rfl⟩ := hx
  rw [wasmEvPendXPS_eq]
  exact J.evRun_pendXP hT hH hE hct hS hts hok hrun hd

/-- **Productive Core runs are productive streams.** -/
theorem coreInf_mem (hT : J.HostOk host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    (hct : J.CT (invoke s a vs)) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hok : InvokeOk s a vs) {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf (profile o) host (invoke s a vs) ω) : ω ∈ wasmEvInfNXP s (a, vs) :=
  J.coreInf_wasmEvInfNXP hT hH hE hct hS hts hok h

end Silmaril.Proofs.Wasm.Abstract.BackInv
