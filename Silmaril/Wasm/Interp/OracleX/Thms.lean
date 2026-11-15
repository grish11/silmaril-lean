module

public import Silmaril.Proofs.Wasm.Interp.OracleSimX
public import Silmaril.Proofs.Wasm.Interp.OracleCloseX
public import Silmaril.Proofs.Wasm.Interp.TypedX
public import Silmaril.Proofs.Wasm.Interp.TypedCloseX
public import Silmaril.Proofs.Wasm.Interp.TailX
public import Silmaril.Proofs.Wasm.Interp.TailCloseX
public import Silmaril.Proofs.Wasm.Interp.TypedT
public import Silmaril.Proofs.Wasm.Interp.TypedCloseT

/-!
# Core 3.0 adequacy of the indirect and reference calls (F4, call forms)

`evalOXT_good`: with a sound oracle (`OracleSoundX`: as `OracleSound`, the
callee's Core run stated for every `call_ref` form), every
`Abstract.CallXT.EvalOXT C` run of code passing the arity check extended by
`irExt` is a Core 3.0 run, with the arity invariants, at every profile and
host. `EvalOXT` is `CallX.EvalOX` whose indirect and reference callees (tail forms included) have
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
  checker `tExt` (adds the three tail forms, `return_call_indirect` and
  `return_call_ref` by their annotated type), `evalOXT_goodT` covers tail
  calls under the tail-aware postcondition (`MatchT`): a resolved tail call
  ends the body in a pending tail call; an unresolved one traps at once or,
  on a null reference, as a pending null tail trapping at the frame
  (`Outcome.tailNull`). At the frame level, the closure on good stores is a
  sound oracle for `tExt` (`oracleSoundT_closedX`): a callee body may end in
  a pending (null) tail call, whose frame exit is closed by
  `funcPost_of_tailRun`/`frame_tail_exit`/`frame_tailNull`. Hence
  `evalOX_closed_goodT`. Callee bodies on good stores have no
  `return_call_ref` (`GoodStoreX`). For typed runs (`TypedT`, checker
  `tExt`) every form is included in callee bodies too:
  `oracleSoundT_typedClosed` and `evalOX_closed_typed_goodT`; a tail
  callee's body is typed from the site's argument types (`retRef_args`,
  `entry_of_invokeOk`), as it runs only after the caller's frame is left.
* The arity premises of `EvalOXT` are discharged from typing in a follow-up
  (for `call_indirect` from the successful `ref.cast`, for `call_ref` from the
  reference's type).
* **The oracle is closed** on good stores (`GoodStoreX`: valid function and
  instance types, bodies without `call_ref`/`return_call_ref` whose indirect calls name instance
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

/-- **Forward simulation with tail calls** (`return_call`, `return_call_indirect`,
`return_call_ref`, checker `tExt`): every `EvalOXT C` run of `tExt`-checked code, with an
oracle sound for `tExt`, is a Core 3.0 run under the tail-aware postcondition `MatchT`. A
resolved tail call ends the body in a pending tail call whose callee ends as the caller's
`.ret` does; an unresolved one is the native trap, reached at once or, on a null reference,
when the frame is left. -/
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

/-- **Typed runs carry their arity premises, tail calls included** (`tExt`). -/
theorem evalOXT_of_typedT {C : Abstract.CallRel H}
    (hC : Silmaril.Wasm.Interp.OracleSoundT P Silmaril.Wasm.Interp.noHostX C)
    (hCk : Abstract.CallXT.KeepsTy C) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : Abstract.CallX.EvalOX C s f stk es r) (ht : Silmaril.Wasm.Interp.TypedT s f stk es) :
    Abstract.CallXT.EvalOXT C s f stk es r :=
  Silmaril.Wasm.Interp.evalOXT_of_typedT hC hCk h ht

/-- **The closure is a sound oracle for typed calls with tail calls** (`tExt`): every call
form in callee bodies included. -/
theorem oracleSoundT_typedClosed :
    Silmaril.Wasm.Interp.OracleSoundT P Silmaril.Wasm.Interp.noHostX
      (Silmaril.Wasm.Interp.CX (Abstract.XRecursion.closedCallX : Abstract.CallRel H)) :=
  Silmaril.Wasm.Interp.oracleSoundT_typedClosed

/-- **Typed closed extended runs are Core 3.0 runs, every call form included**: indirect,
reference and the three tail forms, in the running code and in every callee, no oracle
assumed, under the tail-aware postcondition. -/
theorem evalOX_closed_typed_goodT {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : Abstract.CallX.EvalOX Abstract.XRecursion.closedCallX s f stk es r)
    (ht : Silmaril.Wasm.Interp.TypedT s f stk es) :
    ArityGoodE Silmaril.Wasm.Interp.tExt s f stk es r ∧
      Silmaril.Wasm.Interp.CoreGoodT Silmaril.Wasm.Interp.tExt P Silmaril.Wasm.Interp.noHostX
        s f stk es r :=
  Silmaril.Wasm.Interp.evalOX_closed_typed_goodT h ht

/-! ### Tail calls: the stable shapes for other semantics (regions, CFGs) -/

/-- A `return_call_ref` leaving a frame calls by `call_ref` (`Admin.retToCallIn`). -/
theorem isCallRef_retToCallIn {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst) :
    (c.retToCallIn m).IsCallRef :=
  Silmaril.Wasm.Interp.isCallRef_retToCallIn hc m

/-- **A resolved tail call runs in Core 3.0 to `return_call_ref` on the callee**, within the
caller's frame (`return_call`: its `return_call_ref`-typed form; the indirect forms: the
annotated `return_call_ref y`). The frame replacement happens only when the frame is left. -/
theorem tailRes_steps {s : Store H} {f : Frame} {i : Instr} {stk : List Val} {a : Nat}
    (hres : Abstract.CallX.TailRes s f i stk (some (a, stk.drop (Abstract.CallX.tailPop i)))) :
    ∃ c : Admin, c.IsReturnCallRef ∧
      (∀ d, c = .returnCallRefType d → ∃ fi', s.funcs[a]? = some fi' ∧ d = fi'.type) ∧
      Steps P host ⟨s, f, vals (stk.take (Abstract.CallX.tailPop i)).reverse ++ [.plain i]⟩
        ⟨s, f, [.ref (.func a), c]⟩ :=
  Silmaril.Wasm.Interp.tailRes_steps hres

/-- **An unresolved tail call** runs to a trap, or, on a null reference, to `return_call_ref`
on `ref.null`, a null tail that traps only when the frame is left (`frame_tailNull`). -/
theorem tailRes_none_steps {s : Store H} {f : Frame} {i : Instr} {stk : List Val}
    (hres : Abstract.CallX.TailRes s f i stk none) :
    ∃ (top : Val) (stk' : List Val) (y : TypeIdx), stk = top :: stk' ∧
      (Steps P host ⟨s, f, vals [top] ++ [.plain i]⟩ ⟨s, f, [.trap]⟩ ∨
        Steps P host ⟨s, f, vals [top] ++ [.plain i]⟩
          ⟨s, f, [.ref .null, .plain (.returnCallRef y)]⟩) :=
  Silmaril.Wasm.Interp.tailRes_none_steps hres

end Silmaril.Wasm.Interp.OracleX
