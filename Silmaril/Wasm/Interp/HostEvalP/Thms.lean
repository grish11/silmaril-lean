module

public import Silmaril.Proofs.Wasm.Interp.HostOracleP
public import Silmaril.Proofs.Wasm.Interp.HostDirectP

/-!
# The host oracle for the canonical relation: soundness and coincidence

`Abstract.HostEvalP.hostCallXP host` closes the canonical relation `CallXP.EvalOXP` with host
calls: a Wasm callee by its body (pending tail calls answered when its frame is left, by the same
oracle, so a tail call to a host function is answered by the host there), a host callee by the
host (`Abstract.hostAns`).

**Soundness.** For hosts in the typed host slice (`HostSliceT`: answers extend the
functions keeping the native profile and arity check, values at the declared arity; a host may
throw) that also satisfy `HostSliceE tags` (answers keep the exception checker's store
check `StoreChkE (ehExt tags)` and the tag invariants `TagsOk tags`):

* `hostCallXP_sound`: on stores with the tag invariants, its answers are sound in every
  `call_ref` form (`SoundAnsE`): values, traps and thrown exceptions (of Wasm and host callees)
  are those of Core 3.0 runs of the call with that host;
* `oracleSoundTE_hostP`, `oracleThrowsE_hostP`, `oracleTagsE_hostP`: restricted to such stores
  (`hostP tags host`) it discharges the oracle premises of `PendSim.evalOXP_goodP`;
* `evalOXP_host_good`: every `EvalOXP (hostCallXP host)` run of `ehExt tags`-checked code on a
  store with the tag invariants is a Core 3.0 run with that host, every profile.

`HostSliceE` is needed because `SoundAnsE` asks the answers to keep the exception checker's store
check and the tag invariants, which `HostSliceT` (stated for the native checker) does not
say of host answers. An exception reaches a caller from a Wasm or a host callee, at the call (or
at the frame for a pending tail call), as the semantics says: a host answer `throw t` is one
Core step `call_ref-hostfunc` to `REF.EXN_ADDR t; THROW_REF`. The non-throwing native host
slice is the special case `NativeHostSlice.toT`.

**Coincidence.** On stores whose Wasm functions are direct and exception-free (`StoreDirect`:
`CallX.xFreeL` and `CallXE.ehFreeL` bodies), for hosts keeping that (`HostKeepsDirect`; it is not
implied by `HostSliceT`, whose hosts may append functions with extended call forms or
exception forms):

* `hostCallXP_iff_hostCall`: the canonical host oracle is the native one, `HostEval.hostCall`;
* `bodyCallXP_host_iff`: the body relations agree;
* `evalOXP_host_iff_evalH`: on direct, exception-free code, the canonical flow runs against the
  canonical host oracle are the native runs with host calls `EvalH host`; no such run ends in a
  pending tail call (`CallXP.evalOXP_not_tail`).
-/

public section

namespace Silmaril.Wasm.Interp.HostEvalP

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (EvalH hostCall bodyCall)
open Silmaril.Wasm.Abstract.CallX (xFreeL)
open Silmaril.Wasm.Abstract.CallXE (ehFreeL)
open Silmaril.Wasm.Abstract.CallXP (EvalOXP POut bodyCallXP)
open Silmaril.Wasm.Abstract.HostEvalP (hostCallXP)
open Silmaril.Wasm.Interp (ehExt OracleSoundTE OracleThrowsE OracleTagsE TagsOk ArityGoodP CoreGoodP
  SoundAnsE HostSliceT HostSliceE hostP StoreDirect HostKeepsDirect)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Soundness -/

/-- **The host oracle's answers are sound** on stores with the tag invariants, in every
`call_ref` form. -/
theorem hostCallXP_sound {tags : List TagInst} (hH : HostSliceT host)
    (hE : HostSliceE tags host) (s : Store H) (a : Nat) (us : List Val)
    (out : Store H × Binaryen.Flow) (h : hostCallXP host s a us out) (hts : TagsOk tags s) :
    SoundAnsE tags P host s a us out :=
  Silmaril.Wasm.Interp.hostCallXP_sound hH hE s a us out h hts

theorem oracleSoundTE_hostP {tags : List TagInst} (hH : HostSliceT host)
    (hE : HostSliceE tags host) : OracleSoundTE (ehExt tags) P host (hostP tags host) true :=
  Silmaril.Wasm.Interp.oracleSoundTE_hostP hH hE

theorem oracleThrowsE_hostP {tags : List TagInst} (hH : HostSliceT host)
    (hE : HostSliceE tags host) : OracleThrowsE (ehExt tags) P host (hostP tags host) :=
  Silmaril.Wasm.Interp.oracleThrowsE_hostP hH hE

theorem oracleTagsE_hostP {tags : List TagInst} (hH : HostSliceT host)
    (hE : HostSliceE tags host) : OracleTagsE tags (hostP tags host) :=
  Silmaril.Wasm.Interp.oracleTagsE_hostP hH hE

/-- **Runs against the host oracle are Core 3.0 runs with that host**, all call forms,
exceptions on, every profile. -/
theorem evalOXP_host_good {tags : List TagInst} (hH : HostSliceT host)
    (hE : HostSliceE tags host) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × POut}
    (h : EvalOXP (hostCallXP host) s f stk es r) (hg : TagsOk tags s) :
    TagsOk tags r.1 ∧ ArityGoodP (ehExt tags) s f stk es r true ∧
      CoreGoodP (ehExt tags) P host s f stk es r :=
  Silmaril.Wasm.Interp.evalOXP_host_good hH hE h hg

/-! ## Coincidence with the native host oracle -/

/-- **On direct stores the canonical host oracle is the native one.** -/
theorem hostCallXP_iff_hostCall (hD : HostKeepsDirect host) {s : Store H} (hs : StoreDirect s)
    {a : Nat} {args : List Val} {out : Store H × Binaryen.Flow} :
    hostCallXP host s a args out ↔ hostCall host s a args out :=
  ⟨fun h => (Silmaril.Wasm.Interp.hostCallXP_le_hostCall hD s a args out h hs).1,
    fun h => (Silmaril.Wasm.Interp.hostCall_le_hostCallXP hD s a args out h hs).1⟩

/-- The canonical host oracle keeps direct stores. -/
theorem hostCallXP_direct (hD : HostKeepsDirect host) {s : Store H} (hs : StoreDirect s)
    {a : Nat} {args : List Val} {out : Store H × Binaryen.Flow}
    (h : hostCallXP host s a args out) : StoreDirect out.1 :=
  (Silmaril.Wasm.Interp.hostCallXP_le_hostCall hD s a args out h hs).2

/-- On direct stores, the body relations agree. -/
theorem bodyCallXP_host_iff (hD : HostKeepsDirect host) {s : Store H} (hs : StoreDirect s)
    {a : Nat} {args : List Val} {out : Store H × Binaryen.Flow} :
    bodyCallXP (hostCallXP host) s a args out ↔ bodyCall (hostCall host) s a args out :=
  Silmaril.Wasm.Interp.bodyCallXP_host_iff hD hs

/-- **On direct, exception-free code and stores, canonical runs against the host oracle are the
native runs with host calls.** -/
theorem evalOXP_host_iff_evalH (hD : HostKeepsDirect host) {s : Store H} (hs : StoreDirect s)
    {f : Frame} {stk : List Val} {es : List Binaryen.BExpr} {s' : Store H} {f' : Frame}
    {fl : Binaryen.Flow} (hx : xFreeL es = true) (he : ehFreeL es = true) :
    EvalOXP (hostCallXP host) s f stk es (s', f', .flow fl) ↔ EvalH host s f stk es (s', f', fl) :=
  Silmaril.Wasm.Interp.evalOXP_host_iff_evalH hD hs hx he

end Silmaril.Wasm.Interp.HostEvalP
