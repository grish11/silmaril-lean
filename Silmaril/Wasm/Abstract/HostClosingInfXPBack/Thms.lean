module

public import Silmaril.Wasm.Abstract.HostClosingInfXP.Defs
public import Silmaril.Wasm.Abstract.HostClosingXP.Thms
public import Silmaril.Wasm.Interp.PProgress.Thms
import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.Empty
public import Silmaril.Wasm.Abstract.HostStratXP.Thms
import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.Handler
import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.DivWhole
import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.InfWhole

/-!
# Core to the canonical closure, divergent runs: theorems

Proofs in `Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack`. The backward direction (Core to
canonical) for divergent runs, starting with host-free divergence. Deterministic profile
`SingleThreaded.profile o`; the store may hold host functions.

**Host-free Core divergence is closed canonical divergence** (the base case of divergence after a
log, `LogDivXP.div`, and of `FunDivXP` descents):

* `evalDivXP_of_diverges`: a typed problem (`Interp.TypedP tags`: checked by `ehExt tags` in a
  checked store with the tag invariants, typed in some context, valid instance types) whose Core
  run diverges host-free diverges in the closed canonical semantics (`XDivergeP.EvalDivXP`);
* `funDivXP_of_invoke_diverges`: a typed invocation (`StoreOk s`, `InvokeOk s a vs`,
  `Interp.StoreChkE (Interp.ehExt tags) s.funcs`, `Interp.TagsOk tags s`) diverging host-free in
  Core is `XDivergeP.FunDivXP s a vs`;
* `invoke_diverges_iff_funDivXP_of`: with `Interp.PProgress.invoke_diverges_of_funDivXP`, both ways.
  `Interp.PProgress.invoke_diverges_iff_funDivXP` also assumes a store of Wasm functions only
  (`Interp.WasmFuncsT`); this drops that assumption.

Proof (`Reach`, `Run`, `Progress`, `Closed`): `Interp.evalDivXP_of_noOutcome`'s joint coinduction
with `WasmFuncsT` replaced by the absence of a **closed reach of a host call** (`HReach`,
`HCallReach`: the unfoldings of `DivStepXP`/`CallStepXP`, ending at a call to a host function); the
callee function types then come from typing (`HostClosingXP.funcType_of_indRes`,
`funcType_of_callRef_cfg`, `funcType_of_returnCallRef_site`). A closed reach is a Core run, in any
active context, to a configuration at a host call (the steps of `Interp.progressP`), and a closed
outcome is a Core run to a final form (`Interp.evalOXP_closed_good`); neither has a host-free step,
so neither exists for a problem whose Core run diverges host-free (`diverges_through_steps`).

**Divergence with the empty log**:

* `evalLXPh_of_evalOXP_closed`: a run of the closed canonical semantics `EvalOXP closedCallXP`
  that does not trap is a logged run `EvalLXPh` with the same result whose calls the closure
  resolves to the empty log. Every closed answer (values, an uncaught exception) is a closure
  behaviour with the empty log, by least-fixpoint induction on `closedCallXP` (`Conv`); a trapping
  answer only ends a run in a trap;
* `close_of_closedCallXP_vals`, `close_of_closedCallXP_throw`: per call, a closed answer by
  values (read at the callee's result arity) or by an uncaught exception is a behaviour of
  `Shape.close wasmHOpenXP` with the empty log;
* `wasmEvFunDXP_of_funDivXP`: a call of a function with a function type that diverges at the
  frame (`FunDivXP`) has the behaviour `([], div)` in `wasmEvFunDXP`: a body ending in a pending
  tail call is a descent with no import call to the tail callee, and the chain of such descents
  reaches a body diverging host-free (`LDLwXP` by `LogDivXP.div`) or goes on forever (an infinite
  descent chain, `Shape.closeD`), by choice (`Empty`);
* `wasmEvFunDXP_of_evRun_nil`: a Core run of a typed invocation with no host event, then
  host-free divergence, is `([], div)` in `wasmEvFunDXP`.

**Splitting at a handler** (`Handler`), every profile and host:

* `evDiv_handler_seq_split`: a labelled run with its host events, then host-free divergence, of a
  `try_table` handler in place: the body diverges with the whole log, or runs to a stuck end that
  is not at a host call with a prefix of the log, and the handler around that end goes on with
  the rest (the handler analogue of `evDiv_label_seq_split`).

**Divergence after a log** (`DivBase`, `DivCall`, `DivHead`, `DivTree`, `DivWhole`;
deterministic profile, a host with typed answers in the host slices):

* `evRun_wasmEvFunDXP_div`: a Core run of a typed invocation with the host events `cs`, then
  host-free divergence, is `(cs, div)` in `wasmEvFunDXP`. Proof: strong induction on the length of
  the run to its last event (`EvDiv`), then the size of the trees, as `HostEval`'s `div_wholeL`.
  Each head tree diverges in a part (arguments, condition, a body, a callee; a loop again after
  an iteration branching back, on a strictly shorter run; a frame-level tail call, as the next
  call) or runs to values and the trees after it go on (`evRunN_back_vals`). A finished end of a
  part that should diverge is a resolved logged run, hence a Core run to a final form
  (`evalLXPh_res_evRun`, `wasmEvFunXP_evRun_call`), which rules the divergence out by
  determinism. With no event left, the empty-log case above;
* `wasmEvFunDXP_div_iff`: with `wasmEvFunDXP_div_evRun`, both directions at exactly the log;
* `hostSquareXP_div`: the divergence corner of the exact-log square, unconditionally;
* `backDivXP`: the backward divergence direction `BackDivXP` of `HostStratXP`.

**Productive runs** (`InfSplit`, `InfGoal`, `InfTree`, `InfCtl`, `InfLoop`, `InfWhole`;
deterministic profile, the same hosts):

* `coreInf_wasmEvInfNXP`: a productive Core run of a typed invocation is in `wasmEvInfNXP`, with
  exactly its host events. Proof: as `HostEval`'s `inf_wholeL`. A tree runs productively within
  its function (`InfLXP`, a loop branching back forever by choice of its iterations,
  `InfLXP.loopInf`), or reaches a call whose callee runs productively. A callee runs productively
  within its body, or descends to a reached call or to its frame-level tail call; by choice of
  the descents, finitely many then a productive body (`Shape.closeInfL`), or infinitely many
  (`Shape.closeInf`). In both choices the stream is unbounded: infinitely many iterations or
  descents without a host call would be host-free divergence, which a productive run is not.
  A finished end of a part that should run productively is ruled out by determinism
  (`noInf_of_evRun`);
* `hostObsInf_wasmEvInfNXP_eq`: the Core witness `wasmEvInf` and `wasmEvInfNXP` have the same
  productive observations against the host;
* `backInfXP`: the backward productive direction `BackInfXP` of `HostStratXP`;
* `hostSquareXP_prod`, `hostSquareXP`: the productive corner and the whole exact-log square
  (`FullObs`), unconditionally;
* `coreStratXP_eq_natStratXP`, `coreStratAtXP_eq_natStratAtXP`: **the Core strategy with
  exceptions is the native one** (deterministic profile), on every question of `InvOkXP`, and
  per function.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (TypedP StoreChkE ehExt TagsOk)
open Silmaril.Wasm.Abstract.XDivergeP (EvalDivXP FunDivXP)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {H : Type} {o : GrowOracle} {tags : List TagInst}

/-- **Host-free Core divergence of a typed problem is closed canonical divergence**
(deterministic profile). -/
theorem evalDivXP_of_diverges {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} (ht : TypedP tags s f stk es)
    (hd : Diverges (profile o) (fun _ _ _ _ => False)
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩) :
    EvalDivXP s f stk es :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.evalDivXP_of_diverges ht hd

/-- **Host-free Core divergence of a typed invocation is `FunDivXP`** (deterministic profile),
on a store that may hold host functions. -/
theorem funDivXP_of_invoke_diverges {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hd : Diverges (profile o) (fun _ _ _ _ => False) (invoke s a vs)) : FunDivXP s a vs :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.funDivXP_of_invoke_diverges hs hok hS hts hd

/-- **Host-free Core divergence of a typed invocation is exactly `FunDivXP`** (deterministic
profile), on a store that may hold host functions. -/
theorem invoke_diverges_iff_funDivXP_of {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) :
    Diverges (profile o) (fun _ _ _ _ => False) (invoke s a vs) ↔ FunDivXP s a vs :=
  ⟨funDivXP_of_invoke_diverges hs hok hS hts,
    Silmaril.Wasm.Interp.PProgress.invoke_diverges_of_funDivXP hS hts hok⟩

/-- **A non-trapping closed canonical run is a logged run resolving to the empty log.** -/
theorem evalLXPh_of_evalOXP_closed {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × CallXP.POut}
    (h : CallXP.EvalOXP XRecursionP.closedCallXP s f stk es r) (hn : r.2.2 ≠ .flow .trap) :
    ∃ l, EvalLXPh s f stk es l r ∧
      Silmaril.Games.Abstract.Shape.SubstPre (Silmaril.Games.Abstract.Shape.close wasmHOpenXP)
        (l.map OCall.lift) [] :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.closed_conv h hn

/-- **A closed answer by values is a closure behaviour with the empty log**: the returned values
as the caller reads them (`retVals`, the callee's result arity taken), in the answer's store. -/
theorem close_of_closedCallXP_vals {s s' : Store H} {a : Nat} {us vs : List Val}
    {fl : Binaryen.Flow} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (h : XRecursionP.closedCallXP s a us (s', fl)) (hv : fl.retVals = some vs)
    (hfi : s.funcs[a]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    (([] : List (Silmaril.Games.Abstract.Call (wasmHostSig H))),
      Silmaril.Games.Abstract.End.ret (.inl (vs.take rs.length).reverse) s') ∈
      Silmaril.Games.Abstract.Shape.close wasmHOpenXP a s us :=
  (Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.closed_good _ _ _ _ h).1 vs hv fi ps rs hfi
    hty

/-- **A closed answer by an uncaught exception is a closure behaviour with the empty log**, in
the answer's store. -/
theorem close_of_closedCallXP_throw {s s' : Store H} {a : Nat} {us : List Val} {t : Nat}
    (h : XRecursionP.closedCallXP s a us (s', .throw t)) :
    (([] : List (Silmaril.Games.Abstract.Call (wasmHostSig H))),
      Silmaril.Games.Abstract.End.ret (.inr t) s') ∈
      Silmaril.Games.Abstract.Shape.close wasmHOpenXP a s us :=
  (Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.closed_good _ _ _ _ h).2 t rfl

/-- **A call diverging at the frame has the behaviour `([], div)`**, for a function with a
function type. -/
theorem wasmEvFunDXP_of_funDivXP {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {ps rs : List Validation.CValType} (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hd : FunDivXP s a vs) :
    ([], .div) ∈ wasmEvFunDXP s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.div_of_funDivXP (x := ⟨a, (vs, s)⟩)
    ⟨fi, ps, rs, hfi, hty⟩ hd

/-- **A Core run with no host event, then host-free divergence, is `([], div)`** (deterministic
profile, typed invocations, stores that may hold host functions). -/
theorem wasmEvFunDXP_of_evRun_nil {host : HostSemantics H} {s : Store H} {a : Nat}
    {vs : List Val} {c' : Config H} (hs : StoreOk s) (hok : InvokeOk s a vs)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hrun : EvRun (profile o) host (invoke s a vs) [] c')
    (hd : Diverges (profile o) (fun _ _ _ _ => False) c') :
    ([], .div) ∈ wasmEvFunDXP s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.evRun_nil_div hs hok hS hts hrun hd

/-- **Splitting a handler in place**: the body diverges with the whole log, or runs to a stuck
end that is not at a host call with a prefix of the log, and the handler around that end goes
on with the rest. -/
theorem evDiv_handler_seq_split {P : Numerics.Profile} {host : HostSemantics H} {N : Nat}
    {s : Store H} {f : Frame} {ws : List Val} {n : Nat} {cs₀ : List Catch} {b rest : List Admin}
    {cs : List (Silmaril.Games.Abstract.Call (wasmHostSig H))}
    (h : EvDiv P host N ⟨s, f, vals ws ++ [.handler n cs₀ b] ++ rest⟩ cs) :
    EvDiv P host N ⟨s, f, b⟩ cs ∨
      ∃ (cb : Config H) (N₁ m : Nat) (cs₁ cs₂ : List (Silmaril.Games.Abstract.Call (wasmHostSig H))),
        cs = cs₁ ++ cs₂ ∧ m ≤ N ∧ EvRunN P host N₁ ⟨s, f, b⟩ cs₁ cb ∧
        (∀ c', ¬ Step P SingleThreaded.Det.noHost cb c') ∧
        SingleThreaded.decompose? cb.store cb.code = none ∧
        EvDiv P host m ⟨cb.store, cb.frame, vals ws ++ [.handler n cs₀ cb.code] ++ rest⟩ cs₂ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.evDiv_handler_seq_split h

section Div

open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE)

variable {host : HostSemantics H}

/-- **A Core run with the host events `cs`, then host-free divergence, is `(cs, div)` in
`wasmEvFunDXP`** (deterministic profile; a typed invocation on a checked store with the tag
invariants, which may hold host functions). -/
theorem evRun_wasmEvFunDXP_div (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val}
    {cs : List (Silmaril.Games.Abstract.Call (wasmHostSig H))} {c' : Config H} (hs : StoreOk s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hrun : EvRun (profile o) host (invoke s a vs) cs c')
    (hd : Diverges (profile o) (fun _ _ _ _ => False) c') :
    (cs, .div) ∈ wasmEvFunDXP s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.evRun_div hT hH hE hs hS hts hok hrun hd

/-- **Divergence after exactly the log `cs`, both directions** (deterministic profile). -/
theorem wasmEvFunDXP_div_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val}
    {cs : List (Silmaril.Games.Abstract.Call (wasmHostSig H))} (hs : StoreOk s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    ((cs, .div) ∈ wasmEvFunDXP s (a, vs) ∧ (coreHostRel host).Consistent cs) ↔
      ∃ c', EvRun (profile o) host (invoke s a vs) cs c' ∧
        Diverges (profile o) (fun _ _ _ _ => False) c' :=
  ⟨fun h => wasmEvFunDXP_div_evRun hH hE hts hS hok h.1 h.2,
    fun ⟨_, h, hd⟩ => ⟨evRun_wasmEvFunDXP_div hT hH hE hs hS hts hok h hd, evRun_consistent h⟩⟩

/-- **The divergence corner of the exact-log square**, unconditionally (deterministic profile). -/
theorem hostSquareXP_div (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (cs : List (Silmaril.Games.Abstract.Call (wasmHostSig H))) :
    NatObsXP host s a vs (.div cs) ↔ CoreObsLXP (profile o) host s a vs (.div cs) :=
  hostSquareXP_div_of hH hE hS hts hok
    (fun _ _ h hd => evRun_wasmEvFunDXP_div hT hH hE hs hS hts hok h hd) cs

/-- **The backward divergence direction** of `HostStratXP`, on every question of `InvOkXP`. -/
theorem backDivXP (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host) :
    BackDivXP o host tags :=
  fun _ _ hq _ _ h hd => evRun_wasmEvFunDXP_div hT hH hE hq.1 hq.2.1 hq.2.2.1 hq.2.2.2 h hd

/-! ### Productive runs -/

/-- **A productive Core run of a typed invocation is in `wasmEvInfNXP`**, with exactly its host
events (deterministic profile). -/
theorem coreInf_wasmEvInfNXP (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    {ω : Nat → Silmaril.Games.Abstract.Call (wasmHostSig H)}
    (h : CoreInf (profile o) host (invoke s a vs) ω) : ω ∈ wasmEvInfNXP s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.coreInf_wasmEvInfNXP' hT hH hE hs hS hts hok h

/-- **The productive observations are equal** (deterministic profile): the Core witness and
`wasmEvInfNXP` have the same productive observations against the host. -/
theorem hostObsInf_wasmEvInfNXP_eq (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    Silmaril.Games.Abstract.hostObsInf (coreHostRel host) (wasmEvInf (profile o)) s (a, vs) =
      Silmaril.Games.Abstract.hostObsInf (coreHostRel host) wasmEvInfNXP s (a, vs) :=
  Set.Subset.antisymm (fun _ hω => by
      have h := wasmEvInf_hostObsInf.mp hω
      exact ⟨coreInf_wasmEvInfNXP hT hH hE hs hS hts hok h, fun n => coreInf_consistent h n⟩)
    (hostObsInf_wasmEvInfNXP_le hH hE hts hS hok)

/-- **The backward productive direction** of `HostStratXP`, on every question of `InvOkXP`. -/
theorem backInfXP (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host) :
    BackInfXP o host tags :=
  fun _ _ hq _ h => coreInf_wasmEvInfNXP hT hH hE hq.1 hq.2.1 hq.2.2.1 hq.2.2.2 h

/-- **The productive corner of the exact-log square**, unconditionally (deterministic
profile). -/
theorem hostSquareXP_prod (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (ω : Nat → Silmaril.Games.Abstract.Call (wasmHostSig H)) :
    NatObsXP host s a vs (.prod ω) ↔ CoreObsLXP (profile o) host s a vs (.prod ω) :=
  hostSquareXP_prod_of hH hE hS hts hok
    (fun _ h => coreInf_wasmEvInfNXP hT hH hE hs hS hts hok h) ω

/-- **The exact-log commuting square for the canonical closure** (deterministic profile; a
typed invocation on a checked store with the tag invariants, a host with typed answers in the
host slices): the native and Core observations agree on every full observation. -/
theorem hostSquareXP (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (x : FullObs H) : NatObsXP host s a vs x ↔ CoreObsLXP (profile o) host s a vs x :=
  hostSquareXP_of hT hH hE hs hS hts hok
    (fun _ _ h hd => evRun_wasmEvFunDXP_div hT hH hE hs hS hts hok h hd)
    (fun _ h => coreInf_wasmEvInfNXP hT hH hE hs hS hts hok h) x

/-- **The Core strategy with exceptions is the native one** (deterministic profile), on every
question of `InvOkXP`. -/
theorem coreStratXP_eq_natStratXP (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) :
    coreStratXP (profile o) host (InvOkXP tags) = natStratXP host (InvOkXP tags) :=
  coreStratXP_eq_natStratXP_of hT hH hE (backDivXP hT hH hE) (backInfXP hT hH hE)

/-- **Per function**, final store hidden (deterministic profile). -/
theorem coreStratAtXP_eq_natStratAtXP (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) (s : Store H) (a : Nat) :
    coreStratAtXP (profile o) host (InvOkXP tags) s a = natStratAtXP host (InvOkXP tags) s a :=
  coreStratAtXP_eq_natStratAtXP_of hT hH hE (backDivXP hT hH hE) (backInfXP hT hH hE) s a

end Div

end Silmaril.Wasm.Abstract
