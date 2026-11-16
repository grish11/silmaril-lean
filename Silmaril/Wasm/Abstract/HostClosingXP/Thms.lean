module

public import Silmaril.Wasm.Abstract.HostClosingXP.Defs
public import Silmaril.Wasm.Interp.HostEvalP.Thms
public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.SingleThreaded.Profile
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext
public import Silmaril.Wasm.Interp.PProgress.Thms
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Basic
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Direct
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.TrapClose
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Cut
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackWhole
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackPub
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.PendRun
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackRes
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.TrapExact

/-!
# The canonical relation with host calls as an open module: theorems

Proofs in `Silmaril.Proofs.Wasm.Abstract.HostClosingXP`.

* `evalLXPh_of_evalL`: every native logged run `EvalL` is a canonical logged run `EvalLXPh`,
  ending in the same flow; so `wasmHOpen_le_wasmHOpenXP` and `wasmEvFun_le_wasmEvFunXP` (every
  store).
* `wasmEvFunXP_ret_len`: a function returns at most its result arity; so a cut call is never
  resolved by a return.
* **Traps in the exact store of the trap** (`evalLXPh_trap_exact`, `evalLXPh_cut_exact`,
  `evalLXPh_tail_exact`, `host_trap_exact`, `invoke_trap_exact`): a body trapping itself, at a
  call or at its pending tail call whose callee traps in `s₂`, or a host function answering a
  trap, is a Core run to a trap in exactly that store; `evRun_trap_det` (deterministic profile).
  The closure `wasmEvFunXP` forgets that store (`End.trap`); the session closure
  `HostClosingS.wasmEvFunXPS` keeps it.
* **Coincidence on direct stores** (`Interp.StoreDirect`: Wasm bodies without the extended call
  forms and the exception forms):
  * `wasmHOpenXP_direct`: a canonical open behaviour is a native one, or **cut**: it ends in a
    trap, its log ends in a cut call (an answer of more values than the callee's result arity),
    and answering that call by an exception instead (`inr 0`, ending the function in
    `ret (inr 0)`) is a native open behaviour. Cut behaviours are not native ones, so the open
    modules differ exactly by them;
  * `wasmEvFunXP_direct`: the closures agree, on behaviours whose host answers leave direct
    stores (the host answers are arbitrary in a closure: an answer adding a function with a
    `try_table` leaves the direct fragment, where the native module has no behaviour);
  * `wasmEvFunXP_direct_consistent`: so on behaviours whose log a host keeping direct stores
    (`Interp.HostKeepsDirect`) allows.

**Finished behaviours are Core runs with exactly their log** (H2, forward, every profile; a host
in the native host slice whose answers keep the exception checker's store check and the tag
invariants, `Interp.HostSliceE tags`; a store with the tag invariants `Interp.TagsOk tags` and the
exception checker's store check `Interp.StoreChkE (Interp.ehExt tags)`; a typed invocation):

* `wasmEvFunXP_vals_evRun`: a returning behaviour `(cs, ret (inl ws) s₂)` with a log the host
  allows is a Core run of the invocation whose host events are **exactly** `cs`, to the values
  `ws` at `s₂`;
* `wasmEvFunXP_throw_evRun`: an uncaught exception `(cs, ret (inr t) s₂)` is such a run to the
  thrown exception `throwing t` (`REF.EXN_ADDR t; THROW_REF`) at `s₂`, in the empty frame;
* `wasmEvFunXP_trap_evRun`: a trap `(cs, trap)` is such a run to `[trap]`, in some store (a trap
  carries none).

Proof (`Log`, `Struct`, `Cases`, `Calls`, `Fwd`, `Frame`, `Closure`, `TrapCases`, `TrapFwd`,
`TrapClose`): the cases of `Interp.PendSim.evalOXP_goodP` with logs, by induction on
`EvalLXPh`, each inner logged run lifted through its context (sequence, label, handler, frame;
the glue host-free), the arity facts from `Interp.HostEvalP.evalOXP_host_good` on the
`EvalOXP (hostCallXP host)` run that a logged run, its calls answered consistently, is; and
least-fixpoint induction on the closure. Caught exceptions are the handler's `Catches` steps;
`call_indirect`/`call_ref` reach `call_ref` and run the callee in any `call_ref` form; a frame-level
tail call is the body's run to Core's pending tail call (which passes every label and handler),
`return_call_ref-frame-addr`, then the tail callee in the caller's frame, so a host tail callee is
its one event there. A trapping behaviour resolved by `Shape.Subst.intTrap` is the logged run up
to that call, then the callee's trap leaving every context.

**Core runs are finished behaviours at exactly their log** (H2, backward, deterministic profile
`SingleThreaded.profile o`; a host with typed answers, `HostTyped`, in the native host slice with
`Interp.HostSliceE tags`; a typed store `StoreOk` with the exception checker's store check and the
tag invariants; a typed invocation):

* `evRun_wasmEvFunXP_vals`: a Core run of the invocation with the host events `cs` to the values
  `ws` at `s₂`, in any frame, is the returning behaviour `(cs, ret (inl ws) s₂)`;
* `evRun_wasmEvFunXP_throw`: to the thrown exception `throwing t`, it is `(cs, ret (inr t) s₂)`;
* `evRun_wasmEvFunXP_trap`: to a trap, it is `(cs, trap)`;
* `wasmEvFunXP_vals_iff`, `wasmEvFunXP_throw_iff`, `wasmEvFunXP_trap_iff`: with the forward
  lemmas, both ways (the final frame is the empty frame of the invocation; a trap carries no
  store).

Proof (`BackDet`, `BackSplit`, `BackGoal`, `BackCall`, `BackTy`, `BackSeq`, `BackOps`, `BackCtl`,
`BackBlock`, `BackIf`, `BackWhole`): by strong induction on the length of the labelled run
(`EvRunN`) and on the size of the trees, a run of a typed problem (`Interp.TypedP tags`) whose
end has no host-free step and is not at a host call is read back as a logged canonical run whose
calls resolve to exactly the run's log (or a resolved prefix, then a callee trapping in the
closure, read as a cut call). The run is split at each context (sequence, label, handler and
label, callee frame), the sub-runs read back by induction, the glue host-free (`evRunN_through`
with the forward lemmas of `Interp.Control`, `Interp.EHSim`, `Interp.PendSim`). Where the logged
run ends is read off the forward simulation (`evalLXPh_fwd`, `evalLXPh_trap`) by determinism of
labelled runs with the same log (`evRun_det_end_pre`). A callee is a host event, or its frame
entered (its only step), its body read back and its frame left with values or an exception, a
trap, or a pending tail call made in the caller's frame by `return_call_ref-frame-addr` (the
tail callee read back on the strictly shorter rest of the run, a host tail callee its one event
there). Callee types come from typing: progress at a `call_ref` form, a successful cast for
`return_call_indirect`, the operand's subtyping chain for `return_call_ref`.

`evRunN_back`, `evRunN_back_vals` (for reuse, `HostClosingInfXPBack`): the logged backward
simulation of trees itself, its definitions written out, and read at values.

**Pending calls at exactly their log** (`wasmEvPendXP`: a host function invoked directly, a call
reached in a Wasm body, inside handlers, at `call`, `call_indirect` or `call_ref`, descended into,
or a frame-level tail call to the callee, `PendLXP`):

* `wasmEvPendXP_evRun` (every profile, the hypotheses of the forward lemmas): a pending call
  `(cs, m)` with a log the host allows is a Core run of the invocation with exactly the host
  events `cs`, to a configuration at the host call `m` (`decompose?`), in the store of `m`;
* `evRun_pendXP` (deterministic profile, the hypotheses of the backward lemmas): a Core run of the
  invocation with the host events `cs` to a configuration at a host call `(hh, us)` is the
  pending call `(cs, (hh, c.store, us))`;
* `wasmEvPendXP_evRun_iff`: both directions.

Proof (`PendReach`, `PendClose`, `PendRun`): through the trapping behaviours, at the host
`answerAt host m` that also answers the call `m` by a trap in its store (it keeps every
hypothesis on the host). A pending call answered by a trap is a trapping behaviour of the closure
(a reach is the prefix of a logged run cutting the reached call, resolved by the callee's trap;
a frame-level tail call is resolved the same way), so by `wasmEvFunXP_trap_evRun` a Core run to a
trap, cut at its last event. Conversely the Core run, its call answered by a trap that then
leaves every context, is a trapping Core run, so by `evRun_wasmEvFunXP_trap` a trapping behaviour
of the closure; in every closed behaviour the log before a host event is a pending call of it
(least-fixpoint induction; every logged call of a canonical run is reached).

**Logged runs as Core runs, for reuse** (the hypotheses of the forward lemmas):

* `evalLXPh_evRun`: a logged canonical run whose calls the closure resolves to a log the host
  allows is a run against the canonical host oracle and, from checked code, a Core run with
  exactly that log to a final form matching its result (`evalLXPh_fwd` with `close_le_goodCX`),
  for the simulations of divergent and productive runs (`HostClosingInfXP`);
* `reachLXP_of_evalLXPh`: every logged call of a canonical run is reached, after the calls logged
  before it.
* `evalLXPh_res_evRun`: a logged run resolved by returning callees, or up to a trapping callee,
  is a Core run with exactly its resolved log to a final form (`res_evRun`);
* `wasmEvFunXP_evRun_call`: a closed behaviour of a call is a Core run of the call, in any frame
  and `call_ref` form, with exactly its log to a final form (`close_evRun_call`).

**Facts of the backward simulation, for reuse** (`HostClosingInfXPBack`):

* `outcome_ends_stuck`: a final form (`Outcome.Ends`) has no step, under any host and profile;
* `handlerExit_labelExit`: a handler exit form is a label exit form;
* `evRunN_handler_seq_split`: a labelled run of a handler in place runs its body alone, then the
  handler goes on (as `evRunN_label_seq_split` for a label);
* `evRunN_host_callRef`: a labelled run at a host call in any `call_ref` form ends there, or its
  next event answers the call;
* `funcType_of_callRef_cfg`, `funcType_of_indRes`, `funcType_of_returnCallRef_site`: callee
  function types from typing: a typed `call_ref` form on a function reference, a function entry
  passing an indirect call's cast against a type of the instance with a function type, and a
  typed `return_call_ref` on a function reference.

**Cut calls**:

* `wasmHOpenXP_ne_div`, `wasmEvFunXP_ne_div`: no open behaviour and no closed behaviour ends in
  `div`; a log is a finite list, so no divergence and no productive stream arises from a cut;
* `wasmEvFunXP_cut`: in a resolution against the closure, a cut call (an answer of more values
  than the callee's result arity) is resolved only by `Shape.Subst.intTrap`, at it or at an
  earlier call, never by a return: the resolved behaviour traps, with the resolved prefix's log
  and the trapping callee's log. At the open level a cut answer alone does not force a trap: the
  returning rules (`callRet`, `indRet`, `refRet`) also accept answers of any length and go on, so
  the same log may end in a flow; such behaviours are never resolved past the cut call either.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (StoreDirect)

variable {H : Type}

/-- Every native logged run is a canonical logged run, ending in the same flow. -/
theorem evalLXPh_of_evalL {s s' : Store H} {f f' : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {fl : Flow} (h : EvalL s f stk es l (s', f', fl)) :
    EvalLXPh s f stk es l (s', f', .flow fl) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evalLXPh_of_evalL h

/-- The native open module is included in the canonical one, at every store. -/
theorem wasmHOpen_le_wasmHOpenXP : wasmHOpen (H := H) ≤ wasmHOpenXP :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmHOpen_le

/-- The native closure is included in the canonical one, at every store. -/
theorem wasmEvFun_le_wasmEvFunXP : wasmEvFun (H := H) ≤ wasmEvFunXP :=
  fun s p => Shape.close_mono wasmHOpen_le_wasmHOpenXP p.1 s p.2

/-- **A function returns at most its result arity.** -/
theorem wasmEvFunXP_ret_len {s s' : Store H} {a : Nat} {vs ws : List Val}
    {cs : List (Call (wasmHostSig H))} (h : (cs, .ret (.inl ws) s') ∈ wasmEvFunXP s (a, vs)) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ ws.length ≤ rs.length :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_ret_len h

/-- **On a direct store, a canonical open behaviour is native, or cut.** -/
theorem wasmHOpenXP_direct {a : Nat} {s : Store H} {vs : List Val} (hs : StoreDirect s)
    {x : CallBeh ((wasmHShape H).E ⊕ₛ (wasmHShape H).self) (Store H) (List Val ⊕ Nat)}
    (hx : x ∈ wasmHOpenXP a s vs) :
    x ∈ wasmHOpen a s vs ∨
      (x.2 = .trap ∧ ∃ (pre : List (OCall H)) (a' : Nat) (args : List Val) (s₁ s₂ : Store H)
        (ws : List Val) (fi : FuncInst H) (ps rs : List Validation.CValType),
        x.1 = (pre ++ [OCall.mk a' args s₁ (.inl ws) s₂]).map OCall.lift ∧
        s₁.funcs[a']? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        rs.length < ws.length ∧
        ((pre ++ [OCall.mk a' args s₁ (.inr 0) s₂]).map OCall.lift, .ret (.inr 0) s₂) ∈
          wasmHOpen a s vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmHOpenXP_direct hs hx

/-- **On direct stores the closures agree**, on behaviours whose host answers leave direct
stores. -/
theorem wasmEvFunXP_direct {s : Store H} {a : Nat} {vs : List Val} (hs : StoreDirect s)
    {cs : List (Call (wasmHostSig H))} (hd : ∀ c ∈ cs, StoreDirect c.2.1)
    {e : End (Store H) (List Val ⊕ Nat)} :
    (cs, e) ∈ wasmEvFunXP s (a, vs) ↔ (cs, e) ∈ wasmEvFun s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_direct hs hd

/-- **On direct stores the closures agree on behaviours a host keeping direct stores allows.** -/
theorem wasmEvFunXP_direct_consistent {host : HostSemantics H}
    (hD : Interp.HostKeepsDirect host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreDirect s) {cs : List (Call (wasmHostSig H))}
    (hc : (coreHostRel host).Consistent cs) {e : End (Store H) (List Val ⊕ Nat)} :
    (cs, e) ∈ wasmEvFunXP s (a, vs) ↔ (cs, e) ∈ wasmEvFun s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_direct_consistent hD hs hc

/-! ## Finished behaviours are Core runs with exactly their log -/

section Fwd

open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE TagsOk StoreChkE ehExt)

variable {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H} {tags : List TagInst}

/-- **Returning behaviours are Core runs with exactly their log** (every profile): a returning
behaviour of `wasmEvFunXP` with a log the host allows is a Core run of the invocation whose host
events are exactly that log, to its values. -/
theorem wasmEvFunXP_vals_evRun (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s s₂ : Store H} {a : Nat} {vs ws : List Val} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .ret (.inl ws) s₂) ∈ wasmEvFunXP s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmEvFunXP_ret_evRun hH hE hts hS hok h hc

/-- **Uncaught exceptions are Core runs with exactly their log** (every profile): a behaviour of
`wasmEvFunXP` ending in an uncaught exception, with a log the host allows, is a Core run of the
invocation whose host events are exactly that log, to the thrown exception. -/
theorem wasmEvFunXP_throw_evRun (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s s₂ : Store H} {a : Nat} {vs : List Val} {t : Nat} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .ret (.inr t) s₂) ∈ wasmEvFunXP s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    EvRun P host (invoke s a vs) cs ⟨s₂, {}, throwing t⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmEvFunXP_ret_evRun hH hE hts hS hok h hc

/-- **Traps are Core runs with exactly their log** (every profile): a trapping behaviour of
`wasmEvFunXP` with a log the host allows is a Core run of the invocation whose host events are
exactly that log, to a trap, in some store. -/
theorem wasmEvFunXP_trap_evRun (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s : Store H} {a : Nat} {vs : List Val} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .trap) ∈ wasmEvFunXP s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    ∃ s₂, EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmEvFunXP_trap_evRun hH hE hts hS hok h hc

end Fwd

/-! ## Core runs are finished behaviours at exactly their log -/

section Back

open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE TagsOk StoreChkE ehExt)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {o : GrowOracle} {host : HostSemantics H} {tags : List TagInst}

/-- **Values, with exactly the run's log** (deterministic profile): a Core run of a typed
invocation with the host events `cs` to the values `ws` at `s₂`, in any frame, is the returning
behaviour `(cs, ret (inl ws) s₂)` of `wasmEvFunXP`. -/
theorem evRun_wasmEvFunXP_vals (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs ws : List Val} {f₂ : Frame}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, f₂, vals ws⟩) :
    (cs, .ret (.inl ws) s₂) ∈ wasmEvFunXP s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evRun_wasmEvFunXP_vals hT hH hE hs hS hts hok hrun

/-- **An uncaught exception, with exactly the run's log** (deterministic profile): a Core run of
a typed invocation with the host events `cs` to the thrown exception `throwing t` at `s₂`, in
any frame, is the behaviour `(cs, ret (inr t) s₂)` of `wasmEvFunXP`. -/
theorem evRun_wasmEvFunXP_throw (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs : List Val} {t : Nat} {f₂ : Frame}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, f₂, throwing t⟩) :
    (cs, .ret (.inr t) s₂) ∈ wasmEvFunXP s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evRun_wasmEvFunXP_throw hT hH hE hs hS hts hok hrun

/-- **A trap, with exactly the run's log** (deterministic profile): a Core run of a typed
invocation with the host events `cs` to a trap is the trapping behaviour `(cs, trap)` of
`wasmEvFunXP`. -/
theorem evRun_wasmEvFunXP_trap (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs : List Val} {f₂ : Frame}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, f₂, [.trap]⟩) :
    (cs, .trap) ∈ wasmEvFunXP s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evRun_wasmEvFunXP_trap hT hH hE hs hS hts hok hrun

/-- **Returning behaviours at exactly their log, both directions** (deterministic profile):
`(cs, ret (inl ws) s₂)` is a behaviour of `wasmEvFunXP` with a log the host allows exactly when
the invocation has a Core run with the host events `cs` to the values `ws` at `s₂`, in the empty
frame. -/
theorem wasmEvFunXP_vals_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs ws : List Val}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    ((cs, .ret (.inl ws) s₂) ∈ wasmEvFunXP s (a, vs) ∧ (coreHostRel host).Consistent cs) ↔
      EvRun (profile o) host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ :=
  ⟨fun h => wasmEvFunXP_vals_evRun hH hE hts hS hok h.1 h.2,
    fun h => ⟨evRun_wasmEvFunXP_vals hT hH hE hs hS hts hok h, evRun_consistent h⟩⟩

/-- **Uncaught exceptions at exactly their log, both directions** (deterministic profile):
`(cs, ret (inr t) s₂)` is a behaviour of `wasmEvFunXP` with a log the host allows exactly when
the invocation has a Core run with the host events `cs` to `throwing t` at `s₂`, in the empty
frame. -/
theorem wasmEvFunXP_throw_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs : List Val} {t : Nat}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    ((cs, .ret (.inr t) s₂) ∈ wasmEvFunXP s (a, vs) ∧ (coreHostRel host).Consistent cs) ↔
      EvRun (profile o) host (invoke s a vs) cs ⟨s₂, {}, throwing t⟩ :=
  ⟨fun h => wasmEvFunXP_throw_evRun hH hE hts hS hok h.1 h.2,
    fun h => ⟨evRun_wasmEvFunXP_throw hT hH hE hs hS hts hok h, evRun_consistent h⟩⟩

/-- **Traps at exactly their log, both directions** (deterministic profile): `(cs, trap)` is a
behaviour of `wasmEvFunXP` with a log the host allows exactly when the invocation has a Core run
with the host events `cs` to a trap, in some store (a trap carries none). -/
theorem wasmEvFunXP_trap_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    ((cs, .trap) ∈ wasmEvFunXP s (a, vs) ∧ (coreHostRel host).Consistent cs) ↔
      ∃ s₂, EvRun (profile o) host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ :=
  ⟨fun h => wasmEvFunXP_trap_evRun hH hE hts hS hok h.1 h.2,
    fun ⟨_, h⟩ => ⟨evRun_wasmEvFunXP_trap hT hH hE hs hS hts hok h, evRun_consistent h⟩⟩

/-- **The logged backward simulation of trees** (deterministic profile; `back_all`, its
definitions written out): a labelled Core run of a typed problem with the host events `cs` to an
end with no host-free step, not at a host call, is a logged canonical run whose calls resolve to
exactly `cs`, or to a resolved prefix and then a callee trapping in the closure (the run then
traps), ending as the Core run does: a final form matching the result (`Interp.MatchP`), or a
trap. -/
theorem evRunN_back (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {n : Nat} {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {cs : List (Call (wasmHostSig H))} {c : Config H}
    (ht : Interp.TypedP tags s f stk es)
    (hrun : EvRunN (profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ cs c)
    (hend : ∀ c', ¬ Step (profile o) SingleThreaded.Det.noHost c c')
    (hnd : SingleThreaded.decompose? c.store c.code = none) :
    ∃ (l : List (OCall H)) (r : Store H × Frame × CallXP.POut), EvalLXPh s f stk es l r ∧
      (Shape.SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) cs ∨
        (r.2.2 = .flow .trap ∧ ∃ (l₁ l₂ : List (OCall H)) (g : Nat) (args : List Val)
          (s₁ : Store H) (b : List Val ⊕ Nat) (s₂ : Store H) (q₁ c₁ : List (Call (wasmHostSig H))),
          l = l₁ ++ OCall.mk g args s₁ b s₂ :: l₂ ∧
          Shape.SubstPre (Shape.close wasmHOpenXP) (l₁.map OCall.lift) q₁ ∧
          (c₁, .trap) ∈ Shape.close wasmHOpenXP g s₁ args ∧ cs = q₁ ++ c₁)) ∧
      ((∃ oc : Silmaril.Wasm.Logic.Core.Outcome, oc.Ends c.code ∧ Interp.MatchP r c.store c.frame oc) ∨
        (r.2.2 = .flow .trap ∧ c.code = [.trap])) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.back_end hT hH hE ht hrun hend hnd

/-- **A labelled run of typed trees to values is a normal logged run with exactly its log**
(deterministic profile). -/
theorem evRunN_back_vals (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {n : Nat} {s s₁ : Store H} {f f₁ : Frame} {stk ws : List Val}
    {es : List Binaryen.BExpr} {cs : List (Call (wasmHostSig H))}
    (ht : Interp.TypedP tags s f stk es)
    (hrun : EvRunN (profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ cs ⟨s₁, f₁, vals ws⟩) :
    ∃ (l : List (OCall H)) (stk₁ : List Val), EvalLXPh s f stk es l (s₁, f₁, .flow (.normal stk₁)) ∧
      Shape.SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) cs ∧ ws = stk₁.reverse :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.back_vals hT hH hE ht hrun

end Back

/-! ## Facts of the backward simulation, for reuse -/

section BackFacts

open Silmaril.Wasm.Validation

/-- **A final form has no step**, under any host and profile. -/
theorem outcome_ends_stuck {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    {o : Silmaril.Wasm.Logic.Core.Outcome} {c : List Admin} (he : o.Ends c) (s : Store H)
    (f : Frame) : ∀ c', ¬ Step P host ⟨s, f, c⟩ c' :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.ends_stuck he s f

/-- **A typed `call_ref` form on a function reference: its function has a function type.** -/
theorem funcType_of_callRef_cfg {P : Silmaril.Wasm.Numerics.Profile} {s : Store H} {f : Frame}
    {vs : List Val} {a : Nat} {cr : Admin} {rest : List Admin} {fi : FuncInst H}
    (ht : Sim.ContextTyped ⟨s, f, vals vs ++ .ref (.func a) :: cr :: rest⟩) (hcr : cr.IsCallRef)
    (hfi : s.funcs[a]? = some fi) :
    ∃ ps rs, DefType.funcType? fi.type = some (ps, rs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.funcType_of_callRef_cfg (P := P) ht hcr hfi

/-- **A function entry passing an indirect call's cast has a function type**, against a type of
the instance with a function type. -/
theorem funcType_of_indRes {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {ad : AddrType}
    {i : BitVec ad.intType.width} {fa : Nat} {fi : FuncInst H}
    (hres : CallRes.IndRes s f x y ad i (some fa)) (hfi : s.funcs[fa]? = some fi)
    (hs : CallXT.TyFuncs s) (hm : CallXT.TyTypes f.module) {p : Nat × Nat}
    (hy : CallXT.typeArity f.module y = some p) :
    ∃ ps rs, DefType.funcType? fi.type = some (ps, rs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.funcType_of_indRes hres hfi hs hm hy

/-- **A typed `return_call_ref` on a function reference: its function has a function type.** -/
theorem funcType_of_returnCallRef_site {s : Store H} {f : Frame} {stk : List Val} {fa : Nat}
    {y : TypeIdx} {rest : List Admin} {fi : FuncInst H}
    (ht : Sim.ContextTyped ⟨s, f, vals (.ref (.func fa) :: stk).reverse ++
      .plain (.returnCallRef y) :: rest⟩)
    (hm : CallXT.TyTypes f.module) (hfi : s.funcs[fa]? = some fi) (hfiok : TyOk {} fi.type) :
    ∃ ps rs, DefType.funcType? fi.type = some (ps, rs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.funcType_of_returnCallRef_site ht hm hfi hfiok

/-- **A handler exit form is a label exit form.** -/
theorem handlerExit_labelExit {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {b out : List Admin} (h : HandlerExit s f n cs b out) : ∃ out', LabelExit 0 [] b out' :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.handlerExit_labelExit h

/-- **A labelled run in a handler**: the body runs alone; then the handler around it goes on.
If the body ends at a host call, so does the whole run. -/
theorem evRunN_handler_seq_split {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    {N : Nat} {s : Store H} {f : Frame} {ws : List Val} {n : Nat} {cs₀ : List Catch}
    {b rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host N ⟨s, f, vals ws ++ [.handler n cs₀ b] ++ rest⟩ cs c)
    (hend : ∀ c', ¬ Step P SingleThreaded.Det.noHost c c') :
    ∃ (cb : Config H) (N₁ : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))), cs = cs₁ ++ cs₂ ∧
      N₁ ≤ N ∧ EvRunN P host N₁ ⟨s, f, b⟩ cs₁ cb ∧
      (∀ c', ¬ Step P SingleThreaded.Det.noHost cb c') ∧
      EvRunN P host (N - N₁) ⟨cb.store, cb.frame, vals ws ++ [.handler n cs₀ cb.code] ++ rest⟩
        cs₂ c ∧
      ((SingleThreaded.decompose? cb.store cb.code).isSome →
        cs₂ = [] ∧ c = ⟨cb.store, cb.frame, vals ws ++ [.handler n cs₀ cb.code] ++ rest⟩) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evRunN_handler_seq_split hrun hend

/-- **A labelled run at a host call**, in any `call_ref` form: it ends there with no event, or
its next event answers the call. -/
theorem evRunN_host_callRef {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    {n : Nat} {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
    {hh : H} {ps rs : Ty (.list .val)} {ws us : List Val} {cr : Admin}
    {rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))} (hcr : cr.IsCallRef)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hrun : EvRunN P host n ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: cr :: rest⟩ cs c) :
    (c = ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: cr :: rest⟩ ∧ cs = []) ∨
      ∃ s' r m cs', m < n ∧ cs = ⟨(hh, s, us), (s', r)⟩ :: cs' ∧
        host hh s us (.returned s' r) ∧
        EvRunN P host m ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ cs' c :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evRunN_host_callRef hcr hf hcode he hn hrun

end BackFacts

/-! ## Pending calls at exactly their log -/

section Pend

open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE TagsOk StoreChkE ehExt)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {host : HostSemantics H} {tags : List TagInst}

/-- **Pending calls, natively to Core, at exactly their log** (every profile): a pending call
`(cs, m)` of `wasmEvPendXP` with a log the host allows is a Core run of the invocation with
exactly the host events `cs`, to a configuration at the host call `m`, in the store of `m`. -/
theorem wasmEvPendXP_evRun {P : Silmaril.Wasm.Numerics.Profile} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
    (h : (cs, m) ∈ wasmEvPendXP s (a, vs)) (hc : (coreHostRel host).Consistent cs) :
    ∃ (c : Config H) (E : SingleThreaded.Ctx) (a' : Nat), EvRun P host (invoke s a vs) cs c ∧
      SingleThreaded.decompose? c.store c.code = some (E, a', m.1, m.2.2) ∧ c.store = m.2.1 :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmEvPendXP_evRun hH hE hts hS hok h hc

/-- **Core runs to a host call are pending calls at exactly their log** (deterministic profile):
a Core run of a typed invocation with the host events `cs` to a configuration at a host call
`(hh, us)` is the pending call `(cs, (hh, c.store, us))` of `wasmEvPendXP`. -/
theorem evRun_pendXP {o : GrowOracle} (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    {c : Config H} {cs : List (Call (wasmHostSig H))} {E : SingleThreaded.Ctx} {a' : Nat} {hh : H}
    {us : List Val} (hrun : EvRun (profile o) host (invoke s a vs) cs c)
    (hd : SingleThreaded.decompose? c.store c.code = some (E, a', hh, us)) :
    (cs, (hh, c.store, us)) ∈ wasmEvPendXP s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evRun_pendXP hT hH hE hs hS hts hok hrun hd

/-- **Pending calls at exactly their log, both directions** (deterministic profile):
`(cs, (hh, s', us))` is a pending call of `wasmEvPendXP` with a log the host allows exactly when
the invocation has a Core run with the host events `cs` to a configuration at the host call
`(hh, us)`, in the store `s'`. -/
theorem wasmEvPendXP_evRun_iff {o : GrowOracle} (hT : HostTyped host)
    (hH : NativeHostSlice host) (hE : HostSliceE tags host) {s s' : Store H} {a : Nat}
    {vs us : List Val} {hh : H} {cs : List (Call (wasmHostSig H))} (hs : StoreOk s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    ((cs, (hh, s', us)) ∈ wasmEvPendXP s (a, vs) ∧ (coreHostRel host).Consistent cs) ↔
      ∃ (c : Config H) (E : SingleThreaded.Ctx) (a' : Nat),
        EvRun (profile o) host (invoke s a vs) cs c ∧
        SingleThreaded.decompose? c.store c.code = some (E, a', hh, us) ∧ c.store = s' := by
  constructor
  · exact fun h => wasmEvPendXP_evRun hH hE hts hS hok h.1 h.2
  · rintro ⟨c, E, a', hrun, hd, rfl⟩
    exact ⟨evRun_pendXP hT hH hE hs hS hts hok hrun hd, evRun_consistent hrun⟩

end Pend

/-! ## Cut calls -/

/-- **No open behaviour diverges.** -/
theorem wasmHOpenXP_ne_div {a : Nat} {s : Store H} {vs : List Val}
    {x : CallBeh ((wasmHShape H).E ⊕ₛ (wasmHShape H).self) (Store H) (List Val ⊕ Nat)}
    (hx : x ∈ wasmHOpenXP a s vs) : x.2 ≠ .div :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmHOpenXP_ne_div hx

/-- **No closed behaviour diverges.** -/
theorem wasmEvFunXP_ne_div {s : Store H} {a : Nat} {vs : List Val}
    {cs : List (Call (wasmHostSig H))} : (cs, .div) ∉ wasmEvFunXP s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_ne_div

/-- **In the closure a cut call is resolved only by a trapping callee**: in a resolution against
the closure of a log `u ++ z :: w` whose call `z` is answered by more values than its callee's
result arity, the resolution stops by `Shape.Subst.intTrap` at the `k`-th call, `k ≤ u.length`
(at `z` or before it): the resolved behaviour traps, its log the resolved prefix's log `q` and the
trapping callee's log `c₁`. -/
theorem wasmEvFunXP_cut {g : Nat} {args : List Val} {s₁ s₂ : Store H} {ws : List Val}
    {fi : FuncInst H} {ps rs : List Validation.CValType} (hfi : s₁.funcs[g]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hws : rs.length < ws.length)
    {e : End (Store H) (List Val ⊕ Nat)} {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    {u w : List (HCall H)}
    (h : Shape.Subst (Shape.close wasmHOpenXP)
      (u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w) e y) :
    y.2 = .trap ∧ ∃ (k : Nat) (q c₁ : List (Call (wasmHostSig H))) (g' : Nat) (a' : List Val)
        (s' : Store H) (ans : (List Val ⊕ Nat) × Store H),
        k ≤ u.length ∧
        (u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w).drop k =
          ⟨.inr ⟨g', (a', s')⟩, ans⟩ ::
            (u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w).drop (k + 1) ∧
        Shape.SubstPre (Shape.close wasmHOpenXP)
          ((u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w).take k) q ∧
        (c₁, .trap) ∈ Shape.close wasmHOpenXP g' s' a' ∧ y.1 = q ++ c₁ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_cut hfi hty hws h

/-- **A reach cuts the reached call**: the logged prefix, then the call answered by more values
than its callee returns, is a logged run ending in a trap. -/
theorem reachLXP_cut {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {z : (wasmOShape H).self.Op} (h : ReachLXP s f stk es l z) :
    ∃ (ws : List Val) (f' : Frame),
      EvalLXPh s f stk es (l ++ [OCall.mk z.1 z.2.1 z.2.2 (.inl ws) z.2.2]) (z.2.2, f', .flow .trap) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.reachLXP_cut h

/-! ## Logged runs as Core runs, for reuse -/

section Runs

open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE TagsOk StoreChkE ehExt chkE MatchP)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.HostEvalP (hostCallXP)

variable {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H} {tags : List TagInst}

/-- **A logged canonical run whose calls the closure resolves to a log the host allows** is a run
against the canonical host oracle and, on a store with the tag invariants, from checked code on a
checked store, a Core run with **exactly** that log to a final form matching its result
(`Interp.MatchP`), every profile. The statement behind the finished-behaviour lemmas above, for
the simulations of divergent and productive runs. -/
theorem evalLXPh_evRun (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} {l : List (OCall H)}
    {r : Store H × Frame × POut} {q : List (Call (wasmHostSig H))}
    (h : EvalLXPh s f stk es l r)
    (hq : Shape.SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q)
    (hc : (coreHostRel host).Consistent q) :
    EvalOXP (hostCallXP host) s f stk es r ∧
      (TagsOk tags s → ∀ {labels : List Nat} {ret : Nat} {out : Option Nat},
        StoreChkE (ehExt tags) s.funcs →
        chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
          some out →
        ∃ (s' : Store H) (f' : Frame) (c' : List Admin) (o : Silmaril.Wasm.Logic.Core.Outcome),
          EvRun P host ⟨s, f, vals stk.reverse ++ expression (BExpr.lowerList es)⟩ q
            ⟨s', f', c'⟩ ∧ o.Ends c' ∧ MatchP r s' f' o) := by
  obtain ⟨d, cl⟩ := Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evalLXPh_fwd (P := P) hH hE h q
    (Silmaril.Proofs.Wasm.Abstract.HostClosingXP.substPre_mono
      (Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_le_goodCX hH hE) hq) hc
  exact ⟨d, fun hts _ _ _ hS hchk => cl hts hS hchk⟩

/-- **A logged run resolved by returning callees, or up to a trapping callee, is a Core run with
exactly its resolved log to a final form** (every profile; checked code on a checked store with
the tag invariants). -/
theorem evalLXPh_res_evRun (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} {l : List (OCall H)}
    {r : Store H × Frame × POut} {cs : List (Call (wasmHostSig H))}
    {labels : List Nat} {ret : Nat} {out : Option Nat} (h : EvalLXPh s f stk es l r)
    (hres : Shape.SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) cs ∨
      ∃ (l₁ l₂ : List (OCall H)) (g : Nat) (args : List Val) (s₁ : Store H) (b : List Val ⊕ Nat)
        (s₂ : Store H) (q₁ c₁ : List (Call (wasmHostSig H))),
        l = l₁ ++ OCall.mk g args s₁ b s₂ :: l₂ ∧
        Shape.SubstPre (Shape.close wasmHOpenXP) (l₁.map OCall.lift) q₁ ∧
        (c₁, .trap) ∈ Shape.close wasmHOpenXP g s₁ args ∧ cs = q₁ ++ c₁)
    (hc : (coreHostRel host).Consistent cs) (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs)
    (hchk : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some out) :
    ∃ (s' : Store H) (f' : Frame) (c' : List Admin) (oc : Silmaril.Wasm.Logic.Core.Outcome),
      EvRun P host ⟨s, f, vals stk.reverse ++ expression (BExpr.lowerList es)⟩ cs ⟨s', f', c'⟩ ∧
        oc.Ends c' :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.res_evRun hH hE h hres hc hts hS hchk

/-- **A closed behaviour of a call is a Core run of the call to a final form** with exactly its
log, in any frame and any `call_ref` form (every profile). -/
theorem wasmEvFunXP_evRun_call (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {a : Nat} {s : Store H} {us : List Val} {c₁ : List (Call (wasmHostSig H))}
    {e : End (Store H) (List Val ⊕ Nat)} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hm : (c₁, e) ∈ wasmEvFunXP s (a, us)) (hc : (coreHostRel host).Consistent c₁)
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (f : Frame) (cr : Admin) (hcr : cr.IsCallRef) :
    ∃ (s' : Store H) (code : List Admin) (oc : Silmaril.Wasm.Logic.Core.Outcome), oc.Ends code ∧
      EvRun P host ⟨s, f, vals us ++ [.ref (.func a), cr]⟩ c₁ ⟨s', f, code⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_evRun_call hH hE hm hc hts hS hfi hty hn f cr
    hcr

end Runs

/-! ## Traps in the exact store of the trap -/

section TrapExact

open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE TagsOk StoreChkE ehExt)
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H} {tags : List TagInst}
  {s : Store H} {a : Nat} {us : List Val} {fi : FuncInst H} {ps rs : List Validation.CValType}

/-- **A Wasm body trapping itself traps in the store its logged run ends in** (every profile):
its calls resolved by the closure to a log the host allows, the call is a Core run to a trap in
exactly that store, in any frame and any `call_ref` form. -/
theorem evalLXPh_trap_exact (hH : NativeHostSlice host) (hE : HostSliceE tags host) {fn : Func}
    {s' : Store H} {f₂ : Frame} {l : List (OCall H)} {q : List (Call (wasmHostSig H))}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (hts : TagsOk tags s) (hSt : StoreChkE (ehExt tags) s.funcs)
    (hE' : EvalLXPh s (Frame.forCall fi.module us fn.locals) [] (liftInstrs fn.body) l
      (s', f₂, .flow .trap))
    (hp : Shape.SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q)
    (hq : (coreHostRel host).Consistent q) (f : Frame) (c : Admin) (hcr : c.IsCallRef) :
    EvRun P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ q ⟨s', f, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evalLXPh_trap_exact hH hE hfi hcode hty hn hts hSt
    hE' hp hq f c hcr

/-- **A Wasm body whose call's callee traps in `s₂` traps in `s₂`** (every profile): the calls
before it resolved by the closure to `q`, the callee's Core run to a trap in exactly `s₂` with the
host events `c₁`, the call is a Core run to a trap in exactly `s₂`: the trap leaves every label,
handler and frame without changing the store. -/
theorem evalLXPh_cut_exact (hH : NativeHostSlice host) (hE : HostSliceE tags host) {fn : Func}
    {l l₁ l₂ : List (OCall H)} {r : Store H × Frame × POut} {g : Nat} {args : List Val}
    {s₁ s₂ s₂' : Store H} {b : List Val ⊕ Nat} {q c₁ : List (Call (wasmHostSig H))}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (hts : TagsOk tags s) (hSt : StoreChkE (ehExt tags) s.funcs)
    (hE' : EvalLXPh s (Frame.forCall fi.module us fn.locals) [] (liftInstrs fn.body) l r)
    (hl : l = l₁ ++ OCall.mk g args s₁ b s₂' :: l₂)
    (hp : Shape.SubstPre (Shape.close wasmHOpenXP) (l₁.map OCall.lift) q)
    (hz : ∀ (fi' : FuncInst H) (ps' rs' : List Validation.CValType), s₁.funcs[g]? = some fi' →
      Validation.DefType.funcType? fi'.type = some (ps', rs') → TagsOk tags s₁ →
      StoreChkE (ehExt tags) s₁.funcs → args.length = ps'.length →
      ∀ (f : Frame) (c : Admin), c.IsCallRef →
        EvRun P host ⟨s₁, f, vals args ++ [.ref (.func g), c]⟩ c₁ ⟨s₂, f, [.trap]⟩)
    (hq : (coreHostRel host).Consistent (q ++ c₁)) (f : Frame) (c : Admin) (hcr : c.IsCallRef) :
    EvRun P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ (q ++ c₁) ⟨s₂, f, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evalLXPh_cut_exact hH hE hfi hcode hty hn hts hSt
    hE' hl hp hz hq f c hcr

/-- **A Wasm body whose pending tail call's callee traps in `s₂` traps in `s₂`** (every profile):
the body's run to the pending tail call, its calls resolved by the closure to `q`, the frame
left, and the tail callee's Core run to a trap in exactly `s₂`. -/
theorem evalLXPh_tail_exact (hH : NativeHostSlice host) (hE : HostSliceE tags host) {fn : Func}
    {l : List (OCall H)} {s₁ s₂ : Store H} {f₂ : Frame} {a' n : Nat} {args : List Val}
    {q c₁ : List (Call (wasmHostSig H))}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (hts : TagsOk tags s) (hSt : StoreChkE (ehExt tags) s.funcs)
    (hE' : EvalLXPh s (Frame.forCall fi.module us fn.locals) [] (liftInstrs fn.body) l
      (s₁, f₂, .tail a' args n))
    (hp : Shape.SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q)
    (hz : ∀ (fi' : FuncInst H) (ps' rs' : List Validation.CValType), s₁.funcs[a']? = some fi' →
      Validation.DefType.funcType? fi'.type = some (ps', rs') → TagsOk tags s₁ →
      StoreChkE (ehExt tags) s₁.funcs → args.length = ps'.length →
      ∀ (f : Frame) (c : Admin), c.IsCallRef →
        EvRun P host ⟨s₁, f, vals args ++ [.ref (.func a'), c]⟩ c₁ ⟨s₂, f, [.trap]⟩)
    (hq : (coreHostRel host).Consistent (q ++ c₁)) (f : Frame) (c : Admin) (hcr : c.IsCallRef) :
    EvRun P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ (q ++ c₁) ⟨s₂, f, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evalLXPh_tail_exact hH hE hfi hcode hty hn hts hSt
    hE' hp hz hq f c hcr

/-- **A host function answering a trap that leaves `s'` traps in `s'`**: its one event. -/
theorem host_trap_exact {hh : H} {s' : Store H} (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .host hh) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hn : us.length = ps.length) (hm : host hh s us (.returned s' .trap)) (f : Frame) (c : Admin)
    (hcr : c.IsCallRef) :
    EvRun P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ [⟨(hh, s, us), (s', .trap)⟩]
      ⟨s', f, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.host_trap_exact hfi hcode hty hn hm f c hcr

/-- **An invocation of a function trapping in `s₂`** is a Core run to a trap in `s₂`. -/
theorem invoke_trap_exact {vs : List Val} {s₂ : Store H} {cs : List (Call (wasmHostSig H))}
    (hfi : s.funcs[a]? = some fi)
    (h : ∀ (f : Frame) (c : Admin), c.IsCallRef →
      EvRun P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ cs ⟨s₂, f, [.trap]⟩) :
    EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.invoke_trap_exact hfi h

/-- **Two runs with the same log to a trap trap in the same store and frame** (deterministic
profile). -/
theorem evRun_trap_det {o : Silmaril.Wasm.SingleThreaded.GrowOracle} {K : Config H}
    {q : List (Call (wasmHostSig H))} {s₁ s₂ : Store H} {f₁ f₂ : Frame}
    (h₁ : EvRun (Silmaril.Wasm.SingleThreaded.profile o) host K q ⟨s₁, f₁, [.trap]⟩)
    (h₂ : EvRun (Silmaril.Wasm.SingleThreaded.profile o) host K q ⟨s₂, f₂, [.trap]⟩) :
    s₁ = s₂ ∧ f₁ = f₂ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evRun_trap_det h₁ h₂

end TrapExact

/-- **Every logged call is reached**, after the calls logged before it. -/
theorem reachLXP_of_evalLXPh {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {r : Store H × Frame × CallXP.POut} (h : EvalLXPh s f stk es l r)
    {u w : List (OCall H)} {g : Nat} {args : List Val} {s₁ s₂ : Store H} {b : List Val ⊕ Nat}
    (hl : l = u ++ OCall.mk g args s₁ b s₂ :: w) : ReachLXP s f stk es u ⟨g, (args, s₁)⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.reachLXP_of_log h u w g args s₁ s₂ b hl

end Silmaril.Wasm.Abstract
