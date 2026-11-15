module

public import Silmaril.Proofs.Wasm.Interp.PendSim

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

Definitions in `Silmaril.Proofs.Wasm.Interp.PendSim`.
-/

public section

namespace Silmaril.Wasm.Interp.PendSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (ehExt OracleSoundTE OracleThrowsE OracleTagsE TagsOk ArityGoodP CoreGoodP)

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

end Silmaril.Wasm.Interp.PendSim
