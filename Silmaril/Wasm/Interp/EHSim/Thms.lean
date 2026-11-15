module

public import Silmaril.Proofs.Wasm.Interp.EHSim

/-!
# Core 3.0 adequacy of exceptions (F5)

`evalOXE_good`: with the exception checker `ehExt tags` (`Silmaril.Wasm.Interp.EHExt`) and
exceptions on (`ArityGoodE … true`), every `Abstract.CallXE.EvalOXE C` run of checked code
without the extended call forms (`CallX.xFreeL`) is a Core 3.0 run under `Match`, at every
profile and host:

* `throw x` allocates the exception with the tag's fields and throws it, as `Step.throw` does;
* `throw_ref` traps on null and throws an exception reference;
* `try_table bt cs body` runs as `HANDLER_n{cs} LABEL_n{} …`: values and branches leave both,
  returns and traps pass through, and a thrown exception is resolved by the clauses with the
  existing first-match resolution `Cfg.Region.Catches`: a branch to the clause's label from
  outside the `try_table` with its values (`catch`, `catch_ref`, `catch_all`, `catch_all_ref`),
  or a rethrow;
* a call answered by the oracle may throw (`OracleThrowsE`), and its exception propagates
  through the caller's blocks, loops, conditionals and handlers as a Core throw.

`Match` relates a native `.throw a` to Core's `REF.EXN_ADDR a; THROW_REF` in the same store and
frame (`FlowMatch`).

**Premises.**
* `OracleSoundE (ehExt tags) P host C true`: the oracle is sound with exceptions on (a throwing
  answer satisfies the arity invariant).
* `OracleThrowsE (ehExt tags) P host C`: a throwing answer is a Core run to the exception's
  final form, in every `call_ref` form.
* `OracleTagsE tags C` and `TagsOk tags s`: the run's tag instances are the checker's `tags`, and
  every exception has its tag's field count (`ExnsOk`); `throw` and flat instructions keep this
  (`tagsOk_throw`, `TagsOk.evalFlat`). It makes a caught exception push at least what the
  clause's label expects (`catches_count`).

**Scope.** No extended call forms (`call_indirect`, `call_ref`, tail calls) in the run's code:
their typed cases are stated for `tExt` (`evalOXT_goodT`) and are not yet generalized to
`ehExt`. The oracle premises are not yet discharged by a closure with exceptions.
`evalO_goodEH` covers `EvalO` runs with throwing callees for every stable extension.
-/

public section

namespace Silmaril.Wasm.Interp.EHSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (ehExt OracleSoundE OracleThrowsE OracleTagsE TagsOk ArityGoodE CoreGoodE)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **Forward simulation with exceptions.** -/
theorem evalOXE_good {tags : List TagInst} {C : Abstract.CallRel H}
    (hC : OracleSoundE (ehExt tags) P host C true) (hT : OracleThrowsE (ehExt tags) P host C)
    (hG : OracleTagsE tags C) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : Abstract.CallXE.EvalOXE C s f stk es r) (hx : Abstract.CallX.xFreeL es = true)
    (hts : TagsOk tags s) :
    TagsOk tags r.1 ∧ ArityGoodE (ehExt tags) s f stk es r true ∧
      CoreGoodE (ehExt tags) P host s f stk es r :=
  Silmaril.Wasm.Interp.evalOXE_goodEH hC hT hG h hx hts

/-- **Throwing callees**: with exceptions on, every `EvalO C` run is a Core 3.0 run, the
callees' exceptions included. -/
theorem evalO_good_throws {ext : Silmaril.Wasm.Interp.ExtArity H}
    [Silmaril.Wasm.Interp.ExtStable ext] {C : Abstract.CallRel H}
    (hC : OracleSoundE ext P host C true) (hT : OracleThrowsE ext P host C) {s : Store H}
    {f : Frame} {stk : List Val} {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : Abstract.EvalO C s f stk es r) :
    ArityGoodE ext s f stk es r true ∧ CoreGoodE ext P host s f stk es r :=
  Silmaril.Wasm.Interp.evalO_goodEH hC hT h

end Silmaril.Wasm.Interp.EHSim
