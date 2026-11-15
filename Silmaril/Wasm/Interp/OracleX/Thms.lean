module

public import Silmaril.Proofs.Wasm.Interp.OracleSimX
public import Silmaril.Proofs.Wasm.Interp.OracleCloseX
public import Silmaril.Proofs.Wasm.Interp.TypedX
public import Silmaril.Proofs.Wasm.Interp.TypedCloseX
public import Silmaril.Proofs.Wasm.Interp.TailX
public import Silmaril.Proofs.Wasm.Interp.TailCloseX

/-!
# Core 3.0 adequacy of the indirect and reference calls (F4, call forms)

`evalOXT_good`: with a sound oracle (`OracleSoundX`: as `OracleSound`, the
callee's Core run stated for every `call_ref` form), every
`Abstract.CallXT.EvalOXT C` run of code passing the arity check extended by
`irExt` is a Core 3.0 run, with the arity invariants, at every profile and
host. `EvalOXT` is `CallX.EvalOX` whose `call_indirect`/`call_ref` callees have
the annotated type's counts; it forgets to `EvalOX` (`CallXT.EvalOXT.forget`).

**Scope (intermediate).**

* **Store check.** `ArityGoodE irExt`, `CoreGoodE irExt` and `OracleSoundX`
  assume and preserve `StoreChkE irExt s.funcs`: every function of the store
  passes the extended check, so store functions may hold indirect and
  reference calls. A natively checked store qualifies
  (`storeChkE_of_storeChk`). An oracle answer that appends functions must keep
  `StoreChkE irExt` (`FuncsGoodE irExt`); old functions transfer
  (`storeChk_of_funcsExtE`).
* Tail calls: `irExt` does not describe `return_call*`, so `chkE irExt`
  rejects code containing them and nothing is claimed for it there. With the
  checker `tExt` (adds `return_call x`), `evalOXT_goodT` covers direct tail
  calls under the tail-aware postcondition (`MatchT`, shared step 4);
  `return_call_indirect`/`return_call_ref` stay rejected until the shared
  repair for null tails (`Outcome.tailNull`). At the frame level, the closure
  on good stores is a sound oracle for `tExt` (`oracleSoundT_closedX`): a
  callee body may end in a direct tail call, whose frame exit is closed by
  `funcPost_of_tailRun`/`frame_tail_exit`. Hence `evalOX_closed_goodT`.
* The arity premises of `EvalOXT` are discharged from typing in a follow-up
  (for `call_indirect` from the successful `ref.cast`, for `call_ref` from the
  reference's type).
* **The oracle is closed** on good stores (`GoodStoreX`: valid function and
  instance types, bodies without `call_ref` whose indirect calls name instance
  types): `oracleSoundX_closedX`, by least-fixpoint induction. Hence
  `evalOX_closed_good`: closed extended runs are Core 3.0 runs, no oracle
  assumed. For typed runs (`TypedX`), `call_ref` is included in callee bodies too:
  `oracleSoundX_typedClosed` (the closure, restricted to typed calls, is sound) and
  `evalOX_closed_typed_good`.
-/

public section

namespace Silmaril.Wasm.Interp.OracleX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp (irExt OracleSoundX ArityGoodE CoreGoodE)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **Forward simulation of the indirect and reference calls.** -/
theorem evalOXT_good {C : Abstract.CallRel H} (hC : OracleSoundX P host C) {s : Store H}
    {f : Frame} {stk : List Val} {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : Abstract.CallXT.EvalOXT C s f stk es r) :
    ArityGoodE irExt s f stk es r ∧ CoreGoodE irExt P host s f stk es r :=
  Silmaril.Wasm.Interp.evalOXT_goodE hC h

/-- A sound oracle for every `call_ref` form is sound for `call`, for the store
check extended by `irExt`. -/
theorem oracleSound_of_X {C : Abstract.CallRel H} (hC : OracleSoundX P host C) :
    Silmaril.Wasm.Interp.OracleSoundE irExt P host C :=
  hC.sound

/-- **The closure on good stores is a sound oracle.** -/
theorem oracleSoundX_closedX :
    OracleSoundX P host (Silmaril.Wasm.Interp.closedX (H := H)) :=
  Silmaril.Wasm.Interp.oracleSoundX_closedX

/-- **Closed extended runs are Core 3.0 runs** (indirect calls, good stores, native store
check as above). -/
theorem evalOX_closed_good {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow}
    (h : Abstract.CallX.EvalOX Abstract.XRecursion.closedCallX s f stk es r)
    (hG : Silmaril.Wasm.Interp.GoodStoreX s) (hm : Abstract.CallXT.TyTypes f.module)
    (hx : Abstract.CallXT.indOkL f.module es = true) :
    ArityGoodE irExt s f stk es r ∧ CoreGoodE irExt P host s f stk es r :=
  Silmaril.Wasm.Interp.evalOX_closed_goodE h hG hm hx

/-- **Typed runs carry their arity premises** (both `call_indirect` and `call_ref`):
a run of `irExt`-checked code in an `irExt`-checked store, whose Core configuration is
typed in context, with valid function and instance types and an oracle keeping them, is
an `EvalOXT` run. -/
theorem evalOXT_of_typed {C : Abstract.CallRel H}
    (hC : OracleSoundX P Silmaril.Wasm.Interp.noHostX C) (hCk : Abstract.CallXT.KeepsTy C)
    {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : Abstract.CallX.EvalOX C s f stk es r)
    (ht : Silmaril.Wasm.Interp.TypedX s f stk es) : Abstract.CallXT.EvalOXT C s f stk es r :=
  Silmaril.Wasm.Interp.evalOXT_of_typed hC hCk h ht

/-- **Typed extended runs are Core 3.0 runs**, `call_indirect` and `call_ref` included. -/
theorem evalOX_typed_good {C : Abstract.CallRel H}
    (hC : OracleSoundX P Silmaril.Wasm.Interp.noHostX C) (hCk : Abstract.CallXT.KeepsTy C)
    {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : Abstract.CallX.EvalOX C s f stk es r)
    (ht : Silmaril.Wasm.Interp.TypedX s f stk es) :
    ArityGoodE irExt s f stk es r ∧ CoreGoodE irExt P Silmaril.Wasm.Interp.noHostX s f stk es r :=
  Silmaril.Wasm.Interp.evalOXT_goodE hC (Silmaril.Wasm.Interp.evalOXT_of_typed hC hCk h ht)

/-- **The closure is a sound oracle for typed calls** (callee bodies typed in context,
`TypedEntry`), every call form in callee bodies included. -/
theorem oracleSoundX_typedClosed :
    OracleSoundX P Silmaril.Wasm.Interp.noHostX
      (Silmaril.Wasm.Interp.CX (Abstract.XRecursion.closedCallX : Abstract.CallRel H)) :=
  Silmaril.Wasm.Interp.oracleSoundX_typedClosed

/-- **Typed closed extended runs are Core 3.0 runs**: `call_indirect` and `call_ref` in the
running code and in every callee, no oracle assumed. -/
theorem evalOX_closed_typed_good {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : Abstract.CallX.EvalOX Abstract.XRecursion.closedCallX s f stk es r)
    (ht : Silmaril.Wasm.Interp.TypedX s f stk es) :
    ArityGoodE irExt s f stk es r ∧ CoreGoodE irExt P Silmaril.Wasm.Interp.noHostX s f stk es r :=
  Silmaril.Wasm.Interp.evalOX_closed_typed_good h ht

/-- **Forward simulation with direct tail calls** (`return_call x`, checker `tExt`): every
`EvalOXT C` run of `tExt`-checked code, with an oracle sound for `tExt`, is a Core 3.0 run
under the tail-aware postcondition `MatchT` (a `return_call` ends the body in a pending tail
call whose callee ends as the caller's `.ret` does). `return_call_indirect` and
`return_call_ref` stay rejected: their null case traps only after the frame exits. -/
theorem evalOXT_goodT {C : Abstract.CallRel H} (hC : Silmaril.Wasm.Interp.OracleSoundT P host C)
    {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : Abstract.CallXT.EvalOXT C s f stk es r) :
    ArityGoodE Silmaril.Wasm.Interp.tExt s f stk es r ∧
      Silmaril.Wasm.Interp.CoreGoodT Silmaril.Wasm.Interp.tExt P host s f stk es r :=
  Silmaril.Wasm.Interp.evalOXT_goodT hC h

/-- **The closure on good stores is a sound oracle for `tExt`**: callee bodies may end in a
direct tail call (`return_call x`). -/
theorem oracleSoundT_closedX :
    Silmaril.Wasm.Interp.OracleSoundT P host (Silmaril.Wasm.Interp.closedX (H := H)) :=
  Silmaril.Wasm.Interp.oracleSoundT_closedX

/-- **Closed extended runs with direct tail calls are Core 3.0 runs** (good stores,
`tExt`-checked code, tail-aware postcondition), no oracle assumed. -/
theorem evalOX_closed_goodT {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : Abstract.CallX.EvalOX Abstract.XRecursion.closedCallX s f stk es r)
    (hG : Silmaril.Wasm.Interp.GoodStoreX s) (hm : Abstract.CallXT.TyTypes f.module)
    (hx : Abstract.CallXT.indOkL f.module es = true) :
    ArityGoodE Silmaril.Wasm.Interp.tExt s f stk es r ∧
      Silmaril.Wasm.Interp.CoreGoodT Silmaril.Wasm.Interp.tExt P host s f stk es r :=
  Silmaril.Wasm.Interp.evalOX_closed_goodT h hG hm hx

end Silmaril.Wasm.Interp.OracleX
