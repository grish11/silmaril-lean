module

public import Silmaril.Wasm.Cfg.BridgeCfg.Thms
public import Silmaril.Wasm.Interp.XProgress.Thms
public import Silmaril.Wasm.Abstract.XRecursion.Thms
public import Silmaril.Wasm.Cfg.FunctionCfg.Defs
public import Silmaril.Wasm.Cfg.Machine.Thms
import Silmaril.Proofs.Wasm.Cfg.FunctionCfg
import Silmaril.Proofs.Wasm.Cfg.FunctionDiv

@[expose] public section

/-!
# A defined function's CFG execution against its Core invocation

**The fragment** (stated explicitly): a typed invocation (`StoreOk s`, `InvokeOk s a vs`) of a Wasm
function `fi` with body `fn.body` in a store whose functions are all Wasm functions with function
types (`WasmFuncsT s`) and pass the tail-aware arity check (`Interp.StoreChkE Interp.tExt`), at the
deterministic profile `SingleThreaded.profile o`, with no host (`Interp.noHostX`: the invocation is
closed, so it has no observable call log). The check `tExt` covers every call form, direct,
indirect, by reference and tail; it rejects `throw` and `try_table`, so this fragment has no
exceptions. The machine is the block-CFG machine on `fn.body` in the function's call frame
`Frame.forCall fi.module vs fn.locals`, with calls answered by the typed closed extended oracle
`CX closedCallX` (every call answered by the callee's closed run, on typed entries).

* **`machine_core`**: a machine run from the CFG entry to a sink ends (`EndsC`) as a native run of
  the body (`ResOut`), whose flow is a closed outcome of the invocation (`closedCallX`); Core
  3.0 runs the invocation to the corresponding values (the top `rs` results) or trap, in the same
  final store.
* **`core_machine`**: a Core 3.0 run of the invocation to a normal form is terminal (values or a
  trap), a closed outcome of the invocation, and the native run of the body to it is a machine run
  from the CFG entry to a sink ending as that run. Branches to the function label reach `exit`
  (`Cfg.Machine.MStepC.brOut` …); branches past it are ruled out by the body check (labels
  `[rs.length]`).

* **`invoke_diverges_of_mdivT`** (divergence, soundness): frame divergence of the machine
  (`MDivT`: an infinite run, a finite run to a call of a callee that diverges, or to a tail call
  of one), with the callees `calleeDivX o` names, is Core 3.0 divergence of the invocation. The
  store's function list never changes along the host-free run (`Machine.mdivT_funcs`), so every
  call is from a `tExt`-checked store, where `CX closedCallX` answers as the Core-sound
  `closedXOk`.

* **`invoke_diverges_iff_mdivT`** (divergence, both directions): Core 3.0 divergence of the
  invocation is exactly frame divergence of the machine on the body (`MDivT` with `CX closedCallX`
  and `calleeDivX o`), divergence inside a callee and through a tail callee included. Completeness
  goes through Core: the invocation enters the function's frame, whose divergence is `MDivT`
  (`Machine.frame_div_complete`), the oracle and guard obligations being discharged on the
  fragment (`Proofs.Region.callCompleteG_cx`, `divCallComplete_cx`, `guardedCalls_cx`,
  `tailGuarded_cx`, `tailsOk_of_typed`). **`funDivX_iff_mdivT`**: with
  `invoke_diverges_iff_funDivX`, the native extended divergence `FunDivX` is `MDivT`.

Not claimed here: hosts, exceptions (`tExt` rejects `throw` and `try_table`; no host alone does
not exclude them), and the store-retaining session view.
-/

namespace Silmaril.Wasm.Cfg.Function

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Bridge Silmaril.Wasm.Cfg.Machine
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.XRecursion (closedCallX)

variable {H : Type}

/-- **Machine runs of a function body are invocation results.** -/
theorem machine_core {o : SingleThreaded.GrowOracle} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hS : StoreChkE tExt s.funcs) (hW : WasmFuncsT s)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) {st' : MState H}
    (hrun : Relation.ReflTransGen (MStepC (SingleThreaded.profile o) noHostX
      (CX (closedCallX : Abstract.CallRel H)) fn.body)
      (initial fn.body s (Frame.forCall fi.module vs fn.locals)) st')
    (hsink : st'.node.IsSink) :
    ∃ out s₂ f₂ r, EndsC (CX closedCallX) st' s₂ f₂ out ∧ ResOut (CX closedCallX) s₂ f₂ out r ∧
      Abstract.CallX.EvalOX (CX closedCallX) s (Frame.forCall fi.module vs fn.locals) []
        (liftInstrs fn.body) r ∧
      closedCallX s a vs (r.1, r.2.2) ∧
      (∀ ws, r.2.2.retVals = some ws → Steps (SingleThreaded.profile o) noHostX (invoke s a vs)
        ⟨r.1, {}, vals (ws.take rs.length).reverse⟩) ∧
      (r.2.2 = .trap → Steps (SingleThreaded.profile o) noHostX (invoke s a vs) ⟨r.1, {}, [.trap]⟩) :=
  Proofs.FunctionCfg.machine_core hs hok hS hW hfi hcode hty hrun hsink

/-- **Stopping invocations are machine runs of the function body.** -/
theorem core_machine {o : SingleThreaded.GrowOracle} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hS : StoreChkE tExt s.funcs) (hW : WasmFuncsT s)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) {c' : Config H}
    (hrun : Steps (SingleThreaded.profile o) noHostX (invoke s a vs) c')
    (hnf : ∀ x, ¬ Step (SingleThreaded.profile o) noHostX c' x) :
    c'.Terminal ∧ ∃ (s₂ : Store H) (fl : Flow), closedCallX s a vs (s₂, fl) ∧
      ((∃ ws, fl.retVals = some ws ∧ c' = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
        (fl = .trap ∧ c' = ⟨s₂, {}, [.trap]⟩)) ∧
      ∃ (f₂ : Frame) (st' : MState H) (out : Region.Out) (s₃ : Store H) (f₃ : Frame),
        Abstract.CallX.EvalOX (CX closedCallX) s (Frame.forCall fi.module vs fn.locals) []
          (liftInstrs fn.body) (s₂, f₂, fl) ∧
        Relation.ReflTransGen (MStepC (SingleThreaded.profile o) noHostX
          (CX (closedCallX : Abstract.CallRel H)) fn.body)
          (initial fn.body s (Frame.forCall fi.module vs fn.locals)) st' ∧
        EndsC (CX closedCallX) st' s₃ f₃ out ∧ ResOut (CX closedCallX) s₃ f₃ out (s₂, f₂, fl) :=
  Proofs.FunctionCfg.core_machine hs hok hS hW hfi hcode hty hrun hnf

/-- **Machine frame divergence of a function body is divergence of its invocation**: on the
stated fragment (here: a typed invocation of a function `fi` with body `fn.body` and type
`ps → rs` in a `tExt`-checked store, deterministic profile, no host), `MDivT` with `CX closedCallX`
and `calleeDivX o`, on the body in the call frame from the CFG entry, is Core 3.0 divergence of
`invoke s a vs`. -/
theorem invoke_diverges_of_mdivT {o : SingleThreaded.GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
    (hok : InvokeOk s a vs) (hS : StoreChkE tExt s.funcs) (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (h : MDivT (SingleThreaded.profile o) noHostX (CX (closedCallX : Abstract.CallRel H))
      (calleeDivX o) fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals))) :
    Diverges (SingleThreaded.profile o) noHostX (invoke s a vs) :=
  Proofs.FunctionDiv.invoke_diverges_of_mdivT hok hS hfi hcode hty h

/-- **Divergence of a function's invocation is machine frame divergence of its body**: on the
stated fragment (typed invocation, `WasmFuncsT`, `tExt`-checked store, deterministic profile, no
host), Core 3.0 divergence of `invoke s a vs` holds exactly when `MDivT` with `CX closedCallX` and
`calleeDivX o` holds on the body in the call frame from the CFG entry. -/
theorem invoke_diverges_iff_mdivT {o : SingleThreaded.GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
    (hs : StoreOk s) (hok : InvokeOk s a vs) (hS : StoreChkE tExt s.funcs) (hW : WasmFuncsT s)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    Diverges (SingleThreaded.profile o) noHostX (invoke s a vs) ↔
      MDivT (SingleThreaded.profile o) noHostX (CX (closedCallX : Abstract.CallRel H))
        (calleeDivX o) fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals)) :=
  ⟨Proofs.FunctionDiv.mdivT_of_invoke_diverges hs hok hS hW hfi hcode hty,
    Proofs.FunctionDiv.invoke_diverges_of_mdivT hok hS hfi hcode hty⟩

/-- **Native extended divergence of a function is machine frame divergence of its body**, on the
stated fragment: `FunDivX s a vs` (`Abstract.XDiverge`) holds exactly when `MDivT` does
(`invoke_diverges_iff_funDivX` composed with `invoke_diverges_iff_mdivT`). -/
theorem funDivX_iff_mdivT {o : SingleThreaded.GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
    (hs : StoreOk s) (hok : InvokeOk s a vs) (hS : StoreChkE tExt s.funcs) (hW : WasmFuncsT s)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    Abstract.XDiverge.FunDivX s a vs ↔
      MDivT (SingleThreaded.profile o) noHostX (CX (closedCallX : Abstract.CallRel H))
        (calleeDivX o) fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals)) :=
  ((XProgress.invoke_closedX_adequacy (o := o) hs hok hS hW hfi hty).1.symm).trans
    (invoke_diverges_iff_mdivT hs hok hS hW hfi hcode hty)

end Silmaril.Wasm.Cfg.Function
