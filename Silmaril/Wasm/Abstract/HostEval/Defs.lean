module

public import Silmaril.Wasm.Abstract.Recursion.Defs
public import Silmaril.Wasm.Abstract.HostCall.Defs

/-!
# The native semantics with host calls (stage H2)

`EvalO C` (`Silmaril.Wasm.Abstract.Recursion`) answers every internal call
through an oracle `C`, whatever the callee's code. A host function is
therefore just another oracle answer:

* `resFlow r`: a host result as a callee body flow. Returned values `vs` (Core
  order) are the flow `normal vs.reverse` (top-first); a trap traps; an
  exception throws.
* `hostAns host`: the call of a **host** function at `a` on `args` in `s` may end
  in `(s', resFlow r)` exactly when `host h s args (.returned s' r)`. Host
  divergence and the absence of a host outcome are **not** answers. They are
  the `hostDiv` and `blocked` observations, handled separately
  (`Silmaril.Wasm.Abstract.HostCall`).
* `hostCall host`: the least fixpoint of "run a Wasm callee's body with the
  calls answered by the fixpoint, or answer a host callee by `hostAns`".
* `EvalH host := EvalO (hostCall host)`: terminating native runs with
  internal recursion and host calls, every host answer as the relation allows.

No determinism or totality of `host` is assumed.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- A host result as a callee body flow (values top-first). -/
def resFlow : Result → Flow
  | .values vs => .normal vs.reverse
  | .trap => .trap
  | .throw t => .throw t

/-- Answers of host functions, as the host semantics allows. -/
def hostAns (host : HostSemantics H) : CallRel H := fun s a args out =>
  ∃ (fi : FuncInst H) (h : H) (r : Result), s.funcs[a]? = some fi ∧ fi.code = .host h ∧
    host h s args (.returned out.1 r) ∧ out.2 = resFlow r

/-- One round: Wasm callees by their bodies, host callees by the host. -/
def hostCallOp (host : HostSemantics H) : CallRel H →o CallRel H where
  toFun C := bodyCall C ⊔ hostAns host
  monotone' C C' h s a args out := by
    rintro (h₁ | h₂)
    · exact .inl ((bodyCallOp (H := H)).monotone' h s a args out h₁)
    · exact .inr h₂

/-- **Closing with host calls**: the least fixpoint. -/
def hostCall (host : HostSemantics H) : CallRel H := (hostCallOp host).lfp

/-- **The native semantics with host calls.** -/
abbrev EvalH (host : HostSemantics H) := EvalO (hostCall host)

end Silmaril.Wasm.Abstract
