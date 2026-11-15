module

public import Silmaril.Wasm.Abstract.HostClosing.Defs
import Silmaril.Proofs.Wasm.Abstract.HostClosing.Backward

/-!
# Wasm functions with host calls as an open module: theorems

**The replay links.** The logged closed semantics `wasmEvFun` (host calls as events, internal
calls closed) and the relational native semantics `hostCall host` have the same outcomes,
once the host answers in the log are those the host allows (`HostRel.Consistent` for
`coreHostRel host`):

* `wasmEvFun_hostCall`: a finished behaviour with a consistent log is a `hostCall` outcome,
  through the exit flow;
* `hostCall_wasmEv`: every `hostCall` outcome is a finished behaviour with a consistent log.

Internal Wasm calls never appear in the log; host calls appear in execution order.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type} {host : HostSemantics H}

/-- **Finished replay**: a logged behaviour whose host answers are allowed is a `hostCall`
outcome. -/
theorem wasmEvFun_hostCall {s : Store H} {a : Nat} {vs : List Val}
    {cs : List (Call (wasmHostSig H))} {e : End (Store H) (List Val ⊕ Nat)}
    (h : (cs, e) ∈ wasmEvFun s (a, vs)) (hc : (coreHostRel host).Consistent cs) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H) (bfl fl : Flow),
      s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      hostCall host s a vs (s₂, bfl) ∧ exitFlow rs.length bfl = some fl ∧ e = endOfFlow fl s₂ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosing.close_le_toClosedH a s vs h hc

/-- **Finished replay, converse**: every `hostCall` outcome is a logged behaviour with allowed
host answers. -/
theorem hostCall_wasmEv {s s₂ : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {ps rs : List Validation.CValType} {bfl fl : Flow} (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (h : hostCall host s a vs (s₂, bfl)) (hx : exitFlow rs.length bfl = some fl) :
    ∃ cs, (coreHostRel host).Consistent cs ∧ (cs, endOfFlow fl s₂) ∈ wasmEvFun s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosing.hostCall_le_ofClosedH s a vs _ h fi ps rs fl hfi hty hx

end Silmaril.Wasm.Abstract
