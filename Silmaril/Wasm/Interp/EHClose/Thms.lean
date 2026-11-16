module

public import Silmaril.Proofs.Wasm.Interp.EHClose

/-!
# The closure with exceptions is a sound oracle (F5)

`closedE tags` answers calls by `Abstract.XRecursionE.closedCallXE` — callee bodies run in
`CallXE.EvalOXE`, so callees may throw, catch and rethrow — on good stores (`GoodStoreE tags`:
native bodies without the extended call forms, `XRecursion.StoreXFree`, and the tag invariants
`TagsOk tags`). It discharges every oracle premise of the exception simulation:

* `oracleSoundE_closedE`: sound with exceptions on;
* `oracleThrowsE_closedE`: a callee's thrown exception leaves its label and frame
  (`throw_ref-label`, `throw_ref-frame`) and is a Core throw at the call;
* `oracleTagsE_closedE`: answers keep the tag invariants.

The proof is a least-fixpoint induction: a callee body is a Core run by the exception simulation
(`evalOXE_goodEH`) against the closure restricted to good stores (`GoodStoreE.restrict`).

Hence **`evalOXE_closed_good`**: on a good store, closed runs with exceptions of `ehExt`-checked
code without the extended call forms are Core 3.0 runs, every profile and host, no oracle assumed.

**Status: legacy, restricted scope.** The canonical F5 semantics is `Abstract.CallXP` (pending
tail calls answered only at the frame, faithful under handlers), with closure
`Abstract.XRecursionP.closedCallXP`, Core adequacy `Interp.PendSim` and exact BodyM denotation
`Abstract.ExposeP`. The statements here are for code without the extended call forms (`xFreeL`),
where `CallXP.evalOXP_iff_evalOXE` makes them coincide with the canonical ones; they are not the
factory default for code with tail calls.
-/

public section

namespace Silmaril.Wasm.Interp.EHClose

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (ehExt closedE GoodStoreE OracleSoundE OracleThrowsE OracleTagsE TagsOk
  ArityGoodE CoreGoodE)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- The closure with exceptions is sound, exceptions on. -/
theorem oracleSoundE_closedE (tags : List TagInst) :
    OracleSoundE (ehExt tags) P host (closedE (H := H) tags) true :=
  Silmaril.Wasm.Interp.oracleSoundE_closedE tags

/-- Its thrown exceptions are Core throws. -/
theorem oracleThrowsE_closedE (tags : List TagInst) :
    OracleThrowsE (ehExt tags) P host (closedE (H := H) tags) :=
  Silmaril.Wasm.Interp.oracleThrowsE_closedE tags

/-- Its answers keep the tag invariants. -/
theorem oracleTagsE_closedE (tags : List TagInst) : OracleTagsE tags (closedE (H := H) tags) :=
  Silmaril.Wasm.Interp.oracleTagsE_closedE tags

/-- **Closed runs with exceptions are Core 3.0 runs.** -/
theorem evalOXE_closed_good {tags : List TagInst} {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : Abstract.CallXE.EvalOXE Abstract.XRecursionE.closedCallXE s f stk es r)
    (hg : GoodStoreE tags s) (hx : Abstract.CallX.xFreeL es = true) :
    TagsOk tags r.1 ∧ ArityGoodE (ehExt tags) s f stk es r true ∧
      CoreGoodE (ehExt tags) P host s f stk es r :=
  Silmaril.Wasm.Interp.evalOXE_closed_good h hg hx

end Silmaril.Wasm.Interp.EHClose
