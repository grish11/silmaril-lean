module

public import Silmaril.Wasm.Abstract.HostEvalP.Defs
public import Silmaril.Wasm.Abstract.XRecursionP.Thms
public import Silmaril.Wasm.Binaryen.Behaviour
import Silmaril.Proofs.Wasm.Abstract.HostEvalP.Basic

/-!
# The host oracle for the canonical relation: theorems

* `hostCallXP_fixpoint`: `hostCallXP host` answers a Wasm callee by a run of its body against
  `hostCallXP host` itself (a pending tail call answered when the frame is left, by the same
  oracle, so by the host when the tail callee is a host function), and a host callee by the host.
* `hostCallXP_le`: it is the least such relation (the induction principle).
* `hostCallXPOp_monotone`, `hostCallXP_mono_host`: monotone in the oracle and in the host.
* `hostCallXP_closedHost`: with the closed host (no host function returns) it is
  `XRecursionP.closedCallXP`.
-/

public section

namespace Silmaril.Wasm.Abstract.HostEvalP

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel hostAns)
open Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.XRecursionP

variable {H : Type}

theorem hostCallXP_fixpoint (host : HostSemantics H) :
    hostCallXP host = bodyCallXP (hostCallXP host) ⊔ hostAns host :=
  ((hostCallXPOp host).map_lfp).symm

/-- **Least-fixpoint induction**: a call relation closed under one round contains the oracle. -/
theorem hostCallXP_le {host : HostSemantics H} {C : CallRel H}
    (h : bodyCallXP C ⊔ hostAns host ≤ C) : hostCallXP host ≤ C :=
  OrderHom.lfp_le _ h

theorem hostCallXPOp_monotone (host : HostSemantics H) : Monotone (hostCallXPOp host) :=
  (hostCallXPOp host).monotone

/-- Monotone in the host: more host answers, more answers. -/
theorem hostCallXP_mono_host {host host' : HostSemantics H}
    (h : ∀ hh s vs o, host hh s vs o → host' hh s vs o) : hostCallXP host ≤ hostCallXP host' :=
  Silmaril.Proofs.Wasm.Abstract.HostEvalP.hostCallXP_mono_host h

/-- With the closed host, the host oracle is the closure `closedCallXP`. -/
theorem hostCallXP_closedHost :
    hostCallXP (Binaryen.closedHost : HostSemantics H) = closedCallXP :=
  Silmaril.Proofs.Wasm.Abstract.HostEvalP.hostCallXP_closedHost

end Silmaril.Wasm.Abstract.HostEvalP
