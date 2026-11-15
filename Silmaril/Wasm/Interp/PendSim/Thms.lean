module

public import Silmaril.Proofs.Wasm.Interp.PendSim
public import Silmaril.Proofs.Wasm.Interp.PendClose

/-!
# Forward simulation with pending tail calls (F5)

`Abstract.CallXP.EvalOXP` runs a body to a flow or a **pending tail call**, which passes every
`block`, `loop`, `if` and `try_table` and is made only when the frame is left. Under the exception
checker `ehExt tags`, with exceptions on, every such run of checked code is a Core 3.0 run, for
**all** call forms (direct, indirect and reference calls, and `return_call`,
`return_call_indirect`, `return_call_ref`), every profile and host:

* `MatchP r`: a flow is matched as `Match` does, or a trap is Core's pending null tail call
  (`Outcome.tailNull`, trapping only at the frame); a pending tail call `tail a args n` is Core's
  pending tail call `Outcome.tail (vs₁ ++ args) a c`, in the same store and frame. It leaves
  labels by `return_call_ref-label` and handlers by `return_call_ref-handler`: a `try_table`
  around a tail call does not see the callee;
* `ArityGoodP`: the arity check, a pending tail call returning the function's arity (`POutOk`),
  with its callee well formed (`TailWF`);
* `CoreGoodP`: the Core run under `MatchP`;
* `OracleSoundTE`: a call oracle sound in every `call_ref` form.

**The closure.** `closedP tags` answers calls by `Abstract.XRecursionP.closedCallXP` on stores
with the tag invariants (`TagsOk tags`); callee bodies may contain every call form. A callee's
frame is left as Core leaves it: a pending tail call by `return_call_ref-label` and
`return_call_ref-frame-addr`, the tail callee then answering in the caller's frame; a pending null
tail call by `return_call_ref-frame-null`. By least-fixpoint induction the closure discharges
every oracle premise (`oracleSoundTE_closedP`, `oracleThrowsE_closedP`, `oracleTagsE_closedP`),
so closed runs are Core 3.0 runs, no oracle assumed (`evalOXP_closed_good`).

Definitions in `Silmaril.Proofs.Wasm.Interp.PendSim` and `Silmaril.Proofs.Wasm.Interp.PendClose`.
-/

public section

namespace Silmaril.Wasm.Interp.PendSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (ehExt OracleSoundTE OracleThrowsE OracleTagsE TagsOk ArityGoodP CoreGoodP
  SoundAnsE closedP)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **Forward simulation with pending tail calls**, all call forms, exceptions on. -/
theorem evalOXP_goodP {tags : List TagInst} {C : Abstract.CallRel H}
    (hC : OracleSoundTE (ehExt tags) P host C true) (hT : OracleThrowsE (ehExt tags) P host C)
    (hG : OracleTagsE tags C) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × Abstract.CallXP.POut}
    (h : Abstract.CallXP.EvalOXP C s f stk es r) (hts : TagsOk tags s) :
    TagsOk tags r.1 ∧ ArityGoodP (ehExt tags) s f stk es r true ∧
      CoreGoodP (ehExt tags) P host s f stk es r :=
  Silmaril.Wasm.Interp.evalOXP_goodP hC hT hG h hts

/-- **The closure's answers are sound** on stores with the tag invariants, in every `call_ref`
form: values, traps and thrown exceptions are those of Core runs of the call. -/
theorem closedCallXP_sound (tags : List TagInst) (s : Store H) (a : Nat) (us : List Val)
    (out : Store H × Binaryen.Flow) (h : Abstract.XRecursionP.closedCallXP s a us out)
    (hts : TagsOk tags s) : SoundAnsE tags P host s a us out :=
  Silmaril.Wasm.Interp.closedCallXP_sound tags s a us out h hts

/-- The closure is a sound oracle, exceptions on, in every `call_ref` form. -/
theorem oracleSoundTE_closedP (tags : List TagInst) :
    OracleSoundTE (ehExt tags) P host (closedP (H := H) tags) true :=
  Silmaril.Wasm.Interp.oracleSoundTE_closedP tags

/-- Its thrown exceptions are Core throws. -/
theorem oracleThrowsE_closedP (tags : List TagInst) :
    OracleThrowsE (ehExt tags) P host (closedP (H := H) tags) :=
  Silmaril.Wasm.Interp.oracleThrowsE_closedP tags

/-- Its answers keep the tag invariants. -/
theorem oracleTagsE_closedP (tags : List TagInst) : OracleTagsE tags (closedP (H := H) tags) :=
  Silmaril.Wasm.Interp.oracleTagsE_closedP tags

/-- **Closed runs with pending tail calls are Core 3.0 runs**, all call forms, no oracle
assumed. -/
theorem evalOXP_closed_good {tags : List TagInst} {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × Abstract.CallXP.POut}
    (h : Abstract.CallXP.EvalOXP Abstract.XRecursionP.closedCallXP s f stk es r)
    (hg : TagsOk tags s) :
    TagsOk tags r.1 ∧ ArityGoodP (ehExt tags) s f stk es r true ∧
      CoreGoodP (ehExt tags) P host s f stk es r :=
  Silmaril.Wasm.Interp.evalOXP_closed_good h hg

end Silmaril.Wasm.Interp.PendSim
