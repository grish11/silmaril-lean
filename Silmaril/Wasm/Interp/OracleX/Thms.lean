module

public import Silmaril.Proofs.Wasm.Interp.OracleSimX

/-!
# Core 3.0 adequacy of the indirect and reference calls (F4, call forms)

`evalOXT_good`: with a sound oracle (`OracleSoundX`: as `OracleSound`, the
callee's Core run stated for every `call_ref` form), every
`Abstract.CallXT.EvalOXT C` run of code passing the arity check extended by
`irExt` is a Core 3.0 run, with the arity invariants, at every profile and
host. `EvalOXT` is `CallX.EvalOX` whose `call_indirect`/`call_ref` callees have
the annotated type's counts; it forgets to `EvalOX` (`CallXT.EvalOXT.forget`).

**Scope (intermediate).**

* **Store check.** `ArityGoodE`, `CoreGoodE` and `OracleSoundX` assume
  `StoreChk s.funcs`, the *native* store check: every function of the store
  passes `chk`, which rejects `call_indirect` and `call_ref`. So the theorem is
  non-vacuous only when the running code holds the indirect and reference
  calls and the store's functions do not. Real programs, whose indirect calls
  sit in store functions, are not covered until the store check is
  parameterized by the extension (`StoreChkE irExt`, the shared checker's
  next step).
* Tail calls: `irExt` does not describe `return_call*`, so `chkE irExt`
  rejects code containing them and nothing is claimed for it. A tail call
  replaces the caller's frame in Core 3.0; its adequacy is a frame-level
  statement, still to come.
* The arity premises of `EvalOXT` are discharged from typing in a follow-up
  (for `call_indirect` from the successful `ref.cast`, for `call_ref` from the
  reference's type).
* The oracle is still an oracle: closing it by `XRecursion.closedCallX` and
  showing `OracleSoundX` for the closure on typed stores is part of the same
  completion criterion.
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

/-- A sound oracle for every `call_ref` form is sound for `call`. -/
theorem oracleSound_of_X {C : Abstract.CallRel H} (hC : OracleSoundX P host C) :
    Silmaril.Wasm.Interp.OracleSound P host C :=
  hC.sound

end Silmaril.Wasm.Interp.OracleX
