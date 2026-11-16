module

public import Silmaril.Wasm.Abstract.HostClosingInfXP.Defs
public import Silmaril.Wasm.Abstract.HostClosingXP.Thms
public import Silmaril.Wasm.Abstract.HostClosingInf.Thms
public import Silmaril.Games.Abstract.ModuleDLog.Thms
public import Silmaril.Games.Abstract.ModuleInf.Thms
import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP.Inf

/-!
# Divergence after a log and productive runs of the canonical closure: theorems

Proofs in `Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP`.

**Sanity** (every store):

* `wasmEvFunDXP_of_ne_div`: off `div`, `wasmEvFunDXP` is `wasmEvFunXP` (no new finished
  behaviour, no new log);
* `wasmEvFunDXP_of_evalDivXP`: a Wasm function whose body diverges host-free in the closed
  canonical semantics has the behaviour `([], div)`;
* `infLXP_nil`, `wasmEvInfNXP_of_infLXP`, `closeInf_le_wasmEvInfNXP`: empty trees have no
  productive run; a resolved productive run of a Wasm body, and the productive runs through
  unbounded recursion, are productive runs of the invocation.

**Canonical to Core, every profile** (a host in the native host slice whose answers keep the
exception checker's store check and the tag invariants, `Interp.HostSliceE tags`; a store with
the tag invariants `Interp.TagsOk tags` and the exception checker's store check
`Interp.StoreChkE (Interp.ehExt tags)`; a typed invocation; the hypotheses of the forward
theorems of `HostClosingXP`):

* `wasmEvFunDXP_div_evRun`: a divergent behaviour `(cs, div)` of `wasmEvFunDXP` whose log the
  host allows is a Core run of the invocation with **exactly** the host events `cs`, then
  host-free divergence. Proof (`Glue`, `Reach`, `Desc`): `close` has no `div`; a logged reach, a
  descent (including a frame-level tail call: the body's run to Core's pending tail call, then
  `return_call_ref-frame-addr`) and a logged prefix of host-free divergence are Core runs into a
  hole of an active context, built from `evalLXPh_evRun` piece by piece (a head tree run to
  completion, a loop iteration branching back, an `if` arm, a body entered); an infinite chain of
  descents with finitely many import calls ends in a chain of host-free descents, which is
  `XDivergeP.FunDivXP` by coinduction (a logged run resolving to no import call is a run of the
  closed semantics, `hostCallXP closedHost = closedCallXP`); host-free divergence is Core
  divergence in any context (`Interp.PProgress.diverges_of_evalDivXP`, `diverges_of_funDivXP`);
* `wasmEvInfNXP_coreInf`: every productive run `ω ∈ wasmEvInfNXP` whose answers the host allows
  is a productive Core run of the invocation with exactly the events `ω` (`CoreInf`). Proof
  (`Inf`): a productive run within a function is, by induction, logged Core runs lifted through
  their contexts, ending in a loop iterating forever, a chain of iterations
  (`coreInf_of_segments`, the stream regrouped by iteration); a descent path then a productive
  body, or an infinite chain of descents, is a chain of Core runs;
* `hostObsInf_wasmEvInfNXP_coreInf`, `hostObsInf_wasmEvInfNXP_le`: so the productive
  observations of `wasmEvInfNXP` against such a host are productive Core runs, productive
  observations of the Core witness `wasmEvInf P`.

Not here: the converse directions (Core runs to `wasmEvFunDXP` and `wasmEvInfNXP`).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Binaryen

variable {H : Type}

/-! ## Sanity -/

/-- **Off `div`, `wasmEvFunDXP` is `wasmEvFunXP`.** -/
theorem wasmEvFunDXP_of_ne_div {s : Store H} {a : Nat} {vs : List Val}
    {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)} (hy : y.2 ≠ .div) :
    y ∈ wasmEvFunDXP s (a, vs) ↔ y ∈ wasmEvFunXP s (a, vs) :=
  Shape.mem_closeDLog_of_ne_div hy

/-- **A body diverging host-free diverges with an empty log.** -/
theorem wasmEvFunDXP_of_evalDivXP {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {fn : Func} (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (h : XDivergeP.EvalDivXP s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body)) :
    ([], .div) ∈ wasmEvFunDXP s (a, vs) :=
  .inr ⟨rfl, ⟨a, (vs, s)⟩, [], [], [], .refl _, ⟨fi, fn, [], hf, hcode, .div h, rfl⟩, .nil, rfl⟩

/-- **Empty trees have no productive run.** -/
theorem infLXP_nil {s : Store H} {f : Frame} {stk : List Val} {ω : Nat → OCall H} :
    ¬ InfLXP s f stk [] ω := nofun

/-- **A resolved productive run of a Wasm body** is a productive run of the invocation. -/
theorem wasmEvInfNXP_of_infLXP {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {fn : Func} {ω : Nat → OCall H} {ω' : Nat → Call (wasmHostSig H)}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (h : InfLXP s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) ω)
    (hs : Shape.SubstInf (Shape.close wasmHOpenXP) (fun i => (ω i).lift) ω') :
    ω' ∈ wasmEvInfNXP s (a, vs) :=
  .inr ⟨⟨a, (vs, s)⟩, [], _, ω', .refl _, ⟨fi, fn, ω, hf, hcode, h, rfl⟩, hs,
    (Shape.streamAppend_nil ω').symm⟩

/-- The productive runs through unbounded recursion are productive runs of the invocation. -/
theorem closeInf_le_wasmEvInfNXP {s : Store H} {a : Nat} {vs : List Val} :
    Shape.closeInf wasmHOpenXP a s vs ⊆ wasmEvInfNXP s (a, vs) :=
  Shape.closeInf_subset_closeInfL _ _ _ _ _

/-! ## Canonical to Core -/

section Fwd

open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE TagsOk StoreChkE ehExt)

variable {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H} {tags : List TagInst}

/-- **Divergence after a log is a Core run with exactly that log, then host-free divergence**
(every profile): a divergent behaviour `(cs, div)` of `wasmEvFunDXP` whose log the host allows
is a Core run of the invocation with exactly the host events `cs`, then host-free divergence. -/
theorem wasmEvFunDXP_div_evRun (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s : Store H} {a : Nat} {vs : List Val} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .div) ∈ wasmEvFunDXP s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    ∃ c', EvRun P host (invoke s a vs) cs c' ∧ Diverges P (fun _ _ _ _ => False) c' :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP.wasmEvFunDXP_div_evRun hH hE hts hS hok h hc

/-- **Productive canonical runs are productive Core runs** (every profile): every productive run
of `wasmEvInfNXP` whose answers the host allows is a productive Core run of the invocation with
exactly its events. -/
theorem wasmEvInfNXP_coreInf (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s : Store H} {a : Nat} {vs : List Val} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {ω : Nat → Call (wasmHostSig H)} (h : ω ∈ wasmEvInfNXP s (a, vs))
    (hc : ∀ n, coreHostRel host (ω n).1 (.answer (ω n).2)) :
    CoreInf P host (invoke s a vs) ω :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP.wasmEvInfNXP_coreInf hH hE hts hS hok h hc

/-- **A productive observation of `wasmEvInfNXP` against a host is a productive Core run** of
the invocation with exactly its events (every profile). -/
theorem hostObsInf_wasmEvInfNXP_coreInf (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s : Store H} {a : Nat} {vs : List Val} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {ω : Nat → Call (wasmHostSig H)}
    (h : ω ∈ hostObsInf (coreHostRel host) wasmEvInfNXP s (a, vs)) :
    CoreInf P host (invoke s a vs) ω :=
  wasmEvInfNXP_coreInf hH hE hts hS hok h.1 h.2

/-- **The productive observations of `wasmEvInfNXP` are Core observations** (every profile):
against such a host, `wasmEvInfNXP` observes no productive run that the Core witness
`wasmEvInf P` does not. -/
theorem hostObsInf_wasmEvInfNXP_le (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s : Store H} {a : Nat} {vs : List Val} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs) :
    hostObsInf (coreHostRel host) wasmEvInfNXP s (a, vs) ⊆
      hostObsInf (coreHostRel host) (wasmEvInf P) s (a, vs) :=
  fun _ hω => wasmEvInf_hostObsInf.mpr (hostObsInf_wasmEvInfNXP_coreInf hH hE hts hS hok hω)

end Fwd

end Silmaril.Wasm.Abstract
