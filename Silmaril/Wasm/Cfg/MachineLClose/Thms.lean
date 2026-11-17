module

public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Wasm.Cfg.MachineLProj.Thms
public import Silmaril.Wasm.Abstract.HostClosingS.Defs
public import Silmaril.Wasm.Abstract.XRecursionP.Defs
public import Silmaril.Wasm.Abstract.TypedCat.Thms
import Silmaril.Proofs.Wasm.Cfg.MachineLClose

@[expose] public section

/-!
# The session closure discharges `CloseOk` (H1/H3)

The stepwise projection of the logged machine to `MStepC` (`MachineLProj.proj_initialK`,
`proj_tail_initialK`) assumes every logged call is `CloseOk C` for an arity-respecting oracle `C`.
This topic discharges that assumption for **host-free behaviours of the canonical store-retaining
session closure** `Abstract.wasmEvFunXPS` (equivalently `CfgSession.cfgEvFunXPS`, by
`CfgSession.cfgEvFun_eq`), with `C = fitP closedCallXP` (`TypedCat.arityResp_fitClosed`).

* **`closeOk_of_session`** (no typing hypothesis): a behaviour of the session closure at the
  function `g` on `args` from `s` with the empty host log ends in `.ret b s₂`, and the call
  `SCall.mk g args s b s₂` is a `closedCallXP` answer (`CloseOk closedCallXP`): returned values
  (the callee's top results, trimmed to its result count), an exception, or a callee trap
  (`.inr ()`), each in the store the closure leaves. This includes bodies ending in a pending tail
  call: the closure answers the tail call at the frame, as `CallXP.FrameP.tail` does; its result
  count is the callee's (`evalLXPS_tail_wf`), so trimming agrees. `session_ret`: every session
  behaviour ends in `.ret`.
* **`logged_of_session`**: for a Wasm function `a` of `s` with body `fn.body` and type `(ps, rs)`,
  called with `ps.length` arguments, in a store agreeing with `Γ` (`Γ.Good s`, so its functions
  pass `StoreChkE (ehExt Γ.tags)`), a host-free session behaviour `([], e)` is a logged machine run
  of the body from the CFG entry with **every logged call `CloseOk (fitP closedCallXP)`**:
  * to a sink standing for a body flow (`EndRel`) whose exit flow gives `e` (`endOfFlowS`), or
  * to a block making a pending tail call (`TailL`), its answer `b` also a
    `CloseOk (fitP closedCallXP)` entry, with `e = tailAnsS rs.length n b s₂`.
* **`proj_of_session`**: with `proj_initialK` and `proj_tail_initialK`, the behaviour is an
  `MStepC P host (fitP closedCallXP)` run of the body from the CFG entry (any profile and host):
  to a state related by `ProjRel` to the logged sink, or to the sink the tail answer stands for
  (`tailSink`).

**Fitting.** `fitP` restricts the closure to calls passing the callee's parameter count
(`TypedCat.ArgsFit`). The body's calls fit because the body passes its check
(`TypedCatFit.evalOXP_closed_iff_fit`); the pending tail call fits by
`MachineL.tail_fit_initialK`. The invocation itself must fit (`vs.length = ps.length`): the body's
check (`StoreChkE`) is at `ps.length` parameters, and the frame has `vs.length` of them.
-/

namespace Silmaril.Wasm.Cfg.MachineL

open Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (SCall wasmEvFunXPS endOfFlowS tailAnsS exitFlow wasmHShapeS)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Abstract.TypedCat (fitP arityResp_fitClosed)
open Silmaril.Wasm.Abstract.ExposePStruct (Ctx)

variable {H : Type}

/-- **Every session behaviour ends in `.ret`.** -/
theorem session_ret {s : Store H} {p : Nat × List Val}
    {y : CallBeh (wasmHShapeS H).E (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (h : y ∈ wasmEvFunXPS s p) : ∃ b s₂, y.2 = .ret b s₂ :=
  Proofs.MachineLClose.session_ret h

/-- **A host-free session behaviour of a call is a `closedCallXP` answer**: values, an
exception, or a callee trap, in the store the closure leaves. -/
theorem closeOk_of_session {s s₂ : Store H} {g : Nat} {args : List Val}
    {b : (List Val ⊕ Nat) ⊕ PUnit.{1}} (h : ([], .ret b s₂) ∈ wasmEvFunXPS s (g, args)) :
    CloseOk closedCallXP (SCall.mk g args s b s₂) :=
  Proofs.MachineLClose.closeOk_of_session h

/-- **A host-free session behaviour of a Wasm function is a logged machine run of its body from
the CFG entry**, every logged call answered by the fitting closure: to a sink whose exit flow
gives the end, or to a pending tail call answered by the fitting closure. -/
theorem logged_of_session {Γ : Ctx H} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
    {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})} (hg : Γ.Good s)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hvs : vs.length = ps.length)
    (h : ([], e) ∈ wasmEvFunXPS s (a, vs)) :
    (∃ (l : List (SCall H)) (st : MState H) (s' : Store H) (f₂ : Frame) (bfl fl : Flow),
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
      e = tailAnsS rs.length n b s₂) :=
  Proofs.MachineLClose.logged_of_session hg hfi hcode hty hvs h

/-- **A host-free session behaviour of a Wasm function is an `MStepC` run of its body from the CFG
entry**, calls answered by the fitting closure (any profile and host): to a state related by
`ProjRel` to a logged sink whose exit flow gives the end, or, for a body ending in a pending tail
call, to the sink its answer stands for. -/
theorem proj_of_session {P : Numerics.Profile} {host : HostSemantics H} {Γ : Ctx H}
    {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (hg : Γ.Good s) (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hvs : vs.length = ps.length)
    (h : ([], e) ∈ wasmEvFunXPS s (a, vs)) :
    (∃ (st stC : MState H) (s' : Store H) (f₂ : Frame) (bfl fl : Flow),
      Relation.ReflTransGen (MStepC P host (fitP closedCallXP) fn.body)
        (initial fn.body s (Frame.forCall fi.module vs fn.locals)) stC ∧
      ProjRel st stC ∧ st.node.IsSink ∧ EndRel st (s', f₂, .flow bfl) ∧
      exitFlow rs.length bfl = some fl ∧ e = endOfFlowS fl s') ∨
    (∃ (s₂ : Store H) (f₁ : Frame) (n : Nat) (b : (List Val ⊕ Nat) ⊕ PUnit.{1}),
      Relation.ReflTransGen (MStepC P host (fitP closedCallXP) fn.body)
        (initial fn.body s (Frame.forCall fi.module vs fn.locals)) (tailSink b s₂ f₁) ∧
      e = tailAnsS rs.length n b s₂) :=
  Proofs.MachineLClose.proj_of_session hg hfi hcode hty hvs h

end Silmaril.Wasm.Cfg.MachineL
