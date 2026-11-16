module

public import Silmaril.Wasm.Abstract.XRecursionP.Defs
public import Silmaril.Wasm.Abstract.HostEval.Defs

/-!
# The host oracle for the canonical relation (pending tail calls)

`HostEval.hostCall host` closes the native relation `EvalO` with host calls. This module does the
same for the canonical relation `CallXP.EvalOXP` (exceptions, every call form, tail calls pending
until the frame is left):

* `hostCallXPOp host`: one round — a call of a **Wasm** function is answered by `bodyCallXP`
  (its body run in `EvalOXP`, the frame left by `FrameP`), a call of a **host** function by the
  host (`Abstract.hostAns host`, reused);
* `hostCallXP host`: its least fixpoint.

Since `FrameP` answers a pending tail call by the same oracle, a tail call to a host function is
answered by the host, at the frame (outside every handler of the caller), as in Core 3.0. Host
divergence and the absence of a host outcome are not answers (as for `hostCall`).

Theorems in `Silmaril.Wasm.Abstract.HostEvalP.Thms`; soundness against Core 3.0 and the
coincidence with `HostEval.hostCall` in `Silmaril.Wasm.Interp.HostEvalP.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.HostEvalP

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel hostAns)
open Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.XRecursionP

variable {H : Type}

/-- One round: Wasm callees by their bodies with pending tail calls, host callees by the host. -/
def hostCallXPOp (host : HostSemantics H) : CallRel H →o CallRel H where
  toFun C := bodyCallXP C ⊔ hostAns host
  monotone' C C' h s a args out := by
    rintro (h₁ | h₂)
    · exact .inl ((bodyCallXPOp (H := H)).monotone' h s a args out h₁)
    · exact .inr h₂

/-- **The host oracle for the canonical relation**: the least fixpoint. -/
def hostCallXP (host : HostSemantics H) : CallRel H := (hostCallXPOp host).lfp

end Silmaril.Wasm.Abstract.HostEvalP
