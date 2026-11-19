module

public import Silmaril.Wasm.Cfg.CfgClosure.Thms
public import Silmaril.Wasm.Cfg.MachineLClose.Thms
public import Silmaril.Wasm.Abstract.TypedCatValid.Thms
import Silmaril.Proofs.Wasm.Cfg.CfgValid

@[expose] public section

/-!
# Typed-invocation hypotheses from validation (H3)

The session and CFG-closure theorems take typed-invocation hypotheses. Here they are derived from
the store's validity (`StoreOk`) and the premises of `$invoke` (`InvokeOk`), wherever a derivation
exists:

* the function's type and **the exact parameter count** `vs.length = ps.length`
  (`funcType_of_invokeOk`, from `InvokeOk`);
* the tag invariants `TagsOk s.tags s` and the context hypothesis `Ctx.Good` of the store context
  at the store's own tags (`storeCtx_good_of_storeOk`, from `StoreOk`).

**Still assumed: the exception checker's acceptance `StoreChkE (ehExt s.tags) s.funcs`.** It is
not derivable from module validation alone: the arity checker `Interp.chkE` accepts a fixed
instruction fragment (the native instructions, annotated `select`, the call forms, and with `ehExt`
`throw` and `try_table`), while validated code may use instructions outside it. So it is a
fragment restriction, kept as an explicit hypothesis. Completeness of the checker on validated
bodies inside the fragment is not proved either. On concrete stores it is decided by
`storeChkEB`. The Core corollaries also keep their host hypotheses (`HostTyped`,
`HostSliceT`, `HostSliceE`), which are about the host, not the module.

* `logged_of_valid`, `proj_of_valid`: `MachineLClose.logged_of_session`/`proj_of_session` from
  `StoreOk`, `InvokeOk` and the checker's acceptance.
* `cfgFunDiv_iff_diverges_valid`, `cfgAns_trap_iff_valid`, `cfgAns_vals_iff_valid`,
  `cfgAns_throw_iff_valid`: the `CfgClosure` Core corollaries at the store's own tags, `TagsOk`
  discharged.
-/

namespace Silmaril.Wasm.Cfg.CfgValid

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.CfgClosure Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (SCall wasmEvFunXPS endOfFlowS tailAnsS exitFlow)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Abstract.TypedCat (fitP)
open Silmaril.Wasm.Abstract.TypedCatValid (storeCtx)
open Silmaril.Wasm.Interp (HostSliceT HostSliceE StoreChkE ehExt)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {H : Type}

/-- **An invocation's premises give the function's type and the exact parameter count.** -/
theorem funcType_of_invokeOk {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    (hok : InvokeOk s a vs) (hfi : s.funcs[a]? = some fi) :
    ∃ ps rs : List Validation.CValType,
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ vs.length = ps.length :=
  Proofs.CfgValid.funcType_of_invokeOk hok hfi

/-- **A valid store's context at its own tags is good**, given the checker's acceptance. -/
theorem storeCtx_good_of_storeOk {s : Store H} (hs : StoreOk s)
    (hchk : StoreChkE (ehExt s.tags) s.funcs) : (storeCtx s.tags s hchk).Good s :=
  Proofs.CfgValid.storeCtx_good_of_storeOk hs hchk

/-- **A host-free session behaviour of a validly invoked Wasm function is a logged machine run of
its body**, every logged call answered by the fitting closure (`logged_of_session`, the type,
parameter count and context hypotheses discharged). -/
theorem logged_of_valid {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H} {fn : Func}
    {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})} (hs : StoreOk s)
    (hchk : StoreChkE (ehExt s.tags) s.funcs) (hok : InvokeOk s a vs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (h : ([], e) ∈ wasmEvFunXPS s (a, vs)) :
    ∃ ps rs : List Validation.CValType, Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    ((∃ (l : List (SCall H)) (st : MState H) (s' : Store H) (f₂ : Frame) (bfl fl : Flow),
      MRunL fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals)) l st ∧
      (∀ c ∈ l, CloseOk (fitP closedCallXP) c) ∧ st.node.IsSink ∧
      EndRel st (s', f₂, .flow bfl) ∧ exitFlow rs.length bfl = some fl ∧
      e = endOfFlowS fl s') ∨
    (∃ (l l' : List (SCall H)) (st : MState H) (s₁ s₂ : Store H) (f₁ : Frame) (a' n : Nat)
      (args : List Val) (b : (List Val ⊕ Nat) ⊕ PUnit.{1}),
      MRunL fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals)) l st ∧
      TailL fn.body st l' (s₁, f₁, .tail a' args n) ∧
      (∀ c ∈ l ++ l', CloseOk (fitP closedCallXP) c) ∧
      CloseOk (fitP closedCallXP) (SCall.mk a' args s₁ b s₂) ∧
      e = tailAnsS rs.length n b s₂)) := by
  obtain ⟨ps, rs, hty, hvs⟩ := funcType_of_invokeOk hok hfi
  exact ⟨ps, rs, hty, logged_of_session (storeCtx_good_of_storeOk hs hchk) hfi hcode hty hvs h⟩

/-- **A host-free session behaviour of a validly invoked Wasm function is an `MStepC` run of its
body** (`proj_of_session`, the type, parameter count and context hypotheses discharged). -/
theorem proj_of_valid {P : Numerics.Profile} {host : HostSemantics H} {s : Store H} {a : Nat}
    {vs : List Val} {fi : FuncInst H} {fn : Func}
    {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})} (hs : StoreOk s)
    (hchk : StoreChkE (ehExt s.tags) s.funcs) (hok : InvokeOk s a vs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (h : ([], e) ∈ wasmEvFunXPS s (a, vs)) :
    ∃ ps rs : List Validation.CValType, Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    ((∃ (st stC : MState H) (s' : Store H) (f₂ : Frame) (bfl fl : Flow),
      Relation.ReflTransGen (MStepC P host (fitP closedCallXP) fn.body)
        (initial fn.body s (Frame.forCall fi.module vs fn.locals)) stC ∧
      ProjRel st stC ∧ st.node.IsSink ∧ EndRel st (s', f₂, .flow bfl) ∧
      exitFlow rs.length bfl = some fl ∧ e = endOfFlowS fl s') ∨
    (∃ (s₂ : Store H) (f₁ : Frame) (n : Nat) (b : (List Val ⊕ Nat) ⊕ PUnit.{1}),
      Relation.ReflTransGen (MStepC P host (fitP closedCallXP) fn.body)
        (initial fn.body s (Frame.forCall fi.module vs fn.locals)) (tailSink b s₂ f₁) ∧
      e = tailAnsS rs.length n b s₂)) := by
  obtain ⟨ps, rs, hty, hvs⟩ := funcType_of_invokeOk hok hfi
  exact ⟨ps, rs, hty, proj_of_session (storeCtx_good_of_storeOk hs hchk) hfi hcode hty hvs h⟩

section Core

variable {o : GrowOracle} {host : HostSemantics H}

/-- **CFG callee divergence of a valid invocation is host-free Core divergence.** -/
theorem cfgFunDiv_iff_diverges_valid {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hchk : StoreChkE (ehExt s.tags) s.funcs) :
    cfgFunDiv s a vs ↔ Diverges (profile o) (fun _ _ _ _ => False) (invoke s a vs) :=
  cfgFunDiv_iff_diverges hs hok hchk (Abstract.TypedCatValid.tagsOk_of_storeOk hs)

/-- **A CFG trap answer of a valid invocation is a host-free Core run to a trap.** -/
theorem cfgAns_trap_iff_valid (hT : Abstract.HostTyped host) (hH : HostSliceT host)
    {s s₂ : Store H} (hE : HostSliceE s.tags host) {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hchk : StoreChkE (ehExt s.tags) s.funcs) (hok : InvokeOk s a vs) :
    cfgAns (Abstract.SCall.mk a vs s (.inr ()) s₂) ↔
      Abstract.EvRun (profile o) host (invoke s a vs) [] ⟨s₂, {}, [.trap]⟩ :=
  cfgAns_trap_iff hT hH hE hs hchk (Abstract.TypedCatValid.tagsOk_of_storeOk hs) hok

/-- **A CFG answer by values of a valid invocation is a host-free Core run to them.** -/
theorem cfgAns_vals_iff_valid (hT : Abstract.HostTyped host) (hH : HostSliceT host)
    {s s₂ : Store H} (hE : HostSliceE s.tags host) {a : Nat} {vs ws : List Val} (hs : StoreOk s)
    (hchk : StoreChkE (ehExt s.tags) s.funcs) (hok : InvokeOk s a vs) :
    cfgAns (Abstract.SCall.mk a vs s (.inl (.inl ws)) s₂) ↔
      Abstract.EvRun (profile o) host (invoke s a vs) [] ⟨s₂, {}, vals ws⟩ :=
  cfgAns_vals_iff hT hH hE hs hchk (Abstract.TypedCatValid.tagsOk_of_storeOk hs) hok

/-- **A CFG answer by an exception of a valid invocation is a host-free Core run throwing it.** -/
theorem cfgAns_throw_iff_valid (hT : Abstract.HostTyped host) (hH : HostSliceT host)
    {s s₂ : Store H} (hE : HostSliceE s.tags host) {a : Nat} {vs : List Val} {t : Nat}
    (hs : StoreOk s) (hchk : StoreChkE (ehExt s.tags) s.funcs) (hok : InvokeOk s a vs) :
    cfgAns (Abstract.SCall.mk a vs s (.inl (.inr t)) s₂) ↔
      Abstract.EvRun (profile o) host (invoke s a vs) [] ⟨s₂, {}, throwing t⟩ :=
  cfgAns_throw_iff hT hH hE hs hchk (Abstract.TypedCatValid.tagsOk_of_storeOk hs) hok

end Core

end Silmaril.Wasm.Cfg.CfgValid
