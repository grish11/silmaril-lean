module

public import Silmaril.Wasm.Abstract.BackInv.Defs
public import Silmaril.Wasm.Abstract.HostClosingS.Defs
public import Silmaril.Wasm.Abstract.HostClosingInfXP.Defs
public import Silmaril.Wasm.Abstract.HostSessionXP.Defs
public import Silmaril.Wasm.Abstract.NodeBridge.Defs
public import Silmaril.Wasm.SingleThreaded.Exec.Driver
public import Silmaril.Wasm.Interp.PProgress.Thms
public import Silmaril.Wasm.Interp.HostEvalP.Thms
import Silmaril.Proofs.Wasm.Abstract.BackInv.Through
import Silmaril.Proofs.Wasm.Abstract.BackInv.Session

@[expose] public section

/-!
# The backward simulations for every invariant: theorems

Definitions in `Silmaril.Wasm.Interp.CtxInv.Defs` (`CtxInv`, `BackInv`) and
`Silmaril.Wasm.Abstract.BackInv.Defs` (`backTyped`, `StoreTy`).

**Divergence through host-free steps** (`diverges_through_of`): in the deterministic profile, a
divergent run passes through every host-free step of a configuration in an invariant kept by
host-free steps whose stores have closed-valid principal types (`StoreTy`) and whose code meets
the interpreter's cast side conditions (`DeepAll IHeadInv`). `Sim.ContextTyped` configurations
satisfy both (`storeTy_deepAll_of_ctx`). This is the `through` field of `BackInv` for invariants
whose actual store is not `StoreOk`.

**Core behaviours are session behaviours** (deterministic profile `profile o`; a `BackInv` `J`; a
host in `J.HostOk` in the host slices `Interp.HostSliceT`, `HostSliceE tags`; an invocation in
`J.CT` on a store checked by `ehExt tags` with the tag invariants, with typed arguments):

* `coreBehSXP_mem`: finished behaviours (values, uncaught exceptions, traps in their store,
  divergence after a log) are in `wasmEvFunDXPS`;
* `coreCallout_mem`: callouts are in `wasmEvPendXPS`;
* `coreInf_mem`: productive runs are in `wasmEvInfNXP`.

At `J = backTyped` these are the backward halves of `HostSessionXP.natTripleSXP_eq_coreTripleSXP`.
-/

namespace Silmaril.Wasm.Interp.BackInv

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {H : Type}

/-- **A divergent run passes through every host-free step** of a configuration in an invariant
kept by host-free steps, with closed-valid principal types and the cast side conditions. -/
theorem diverges_through_of {o : GrowOracle} {host : HostSemantics H} {I : Config H → Prop}
    (hI : ∀ c, I c → StoreTy c.store ∧ SingleThreaded.Exec.DeepAll SingleThreaded.Exec.IHeadInv
      c.frame c.code)
    (hstep : ∀ c c', I c → SingleThreaded.Det.DStep o c c' → I c') {K d : Config H} (ht : I K)
    (hK : Diverges (profile o) host K) (hd : SingleThreaded.Det.DStep o K d) :
    Diverges (profile o) host d :=
  Silmaril.Proofs.Wasm.Abstract.BackInv.diverges_through_of hI hstep ht hK hd

/-- `Sim.ContextTyped` configurations have closed-valid principal types and the cast side
conditions. -/
theorem storeTy_deepAll_of_ctx {c : Config H} (h : Sim.ContextTyped c) :
    StoreTy c.store ∧ SingleThreaded.Exec.DeepAll SingleThreaded.Exec.IHeadInv c.frame c.code :=
  Silmaril.Proofs.Wasm.Abstract.BackInv.storeTy_deepAll_of_ctx h

variable (J : BackInv H) {o : GrowOracle} {host : HostSemantics H} {tags : List TagInst}
  {s : Store H} {a : Nat} {vs : List Val}

/-- **Finished Core behaviours are session behaviours**, for every invariant. -/
theorem coreBehSXP_mem (hT : J.HostOk host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    (hct : J.CT (invoke s a vs)) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hok : InvokeOk s a vs) {y : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit)}
    (hy : CoreBehSXP (profile o) host s (a, vs) y) : y ∈ wasmEvFunDXPS s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.BackInv.coreBehSXP_mem J hT hH hE hct hS hts hok hy

/-- **Core callouts are pending session calls**, for every invariant. -/
theorem coreCallout_mem (hT : J.HostOk host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    (hct : J.CT (invoke s a vs)) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hok : InvokeOk s a vs) {x : List (Call (wasmHostSig H)) × (wasmHostSig H).Op}
    (hx : NodeBridge.CoreCallout (profile o) host s (a, vs) x) : x ∈ wasmEvPendXPS s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.BackInv.coreCallout_mem J hT hH hE hct hS hts hok hx

/-- **Productive Core runs are productive streams**, for every invariant. -/
theorem coreInf_mem (hT : J.HostOk host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    (hct : J.CT (invoke s a vs)) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hok : InvokeOk s a vs) {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf (profile o) host (invoke s a vs) ω) : ω ∈ wasmEvInfNXP s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.BackInv.coreInf_mem J hT hH hE hct hS hts hok h

end Silmaril.Wasm.Interp.BackInv
