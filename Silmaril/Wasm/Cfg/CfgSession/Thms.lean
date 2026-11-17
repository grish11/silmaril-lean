module

public import Silmaril.Wasm.Cfg.CfgSession.Defs
public import Silmaril.Wasm.Abstract.HostClosingS.Thms
import Silmaril.Proofs.Wasm.Cfg.CfgSession

@[expose] public section

/-!
# The recursive CFG closure: theorems (H3, finished behaviours)

* **`cfgHOpen_eq`**: the CFG open module `cfgHOpenXPS` is the session's open module
  `Abstract.wasmHOpenXPS`. For every function, store and arguments, its behaviours are the same:
  the logs, ends and stores of finished Wasm bodies, pending tail calls with their answers, and
  host calls.
  * ⊆: `MachineL.forward_sink`, `forward_tail`. The end a sink stands for is the same for every
    native flow it stands for (`exitFlow_endRel`).
  * ⊇: `MachineL.backward`. Its excluded native outcome, `brk (k + 1)`, has no framed end
    (`exitFlow` gives `none`).
  Every statement is for all code, with no typing, every call form, and exceptions on; traps
  keep their store.
* **`cfgEvFun_eq`**: the CFG session closure `cfgEvFunXPS = Shape.close cfgHOpenXPS` is the
  store-retaining session closure `Abstract.wasmEvFunXPS`.

The closure resolves internal calls and tail calls through functions **run on the CFG machine**:
the recursion is the CFG's own, not the native relation's. Every theorem about `wasmEvFunXPS`
holds for it by `cfgEvFun_eq`: erasure to `wasmEvFunXP` (`HostClosingS.wasmEvFunXPS_erase`), and
Core 3.0 adequacy with hosts and exceptions (`wasmEvFunXPS_trap_iff`, `wasmEvFunXPS_vals_iff`, …).

* **`cfgPend_iff`**, **`cfgEvPend_eq`** (pending host calls): the CFG session's pending host calls
  (`CfgPendLXPS`: a host function at once; a Wasm body run on the machine to a block reaching an
  internal call, `ReachL`, or to a pending tail call, `TailL`, its log resolved by the CFG closure)
  are the session's (`Abstract.PendLXPS`, `wasmEvPendXPS`). The proof uses
  `MachineL.pending_iff`, `forward_tail` and `backward`, and `cfgHOpen_eq` for the closure that
  resolves the logs.

* **`cfgHOpenX_eq`**, **`cfgEvFunX_eq`** (the canonical, trap-erasing module): the open module
  `cfgHOpenXP`, run on the logged machine with its session logs read as canonical logs
  (`CanonRead`: the reading `OCall.toS`, or a final callee-trap answer read as a cut call, for
  every answer longer than the callee's result arity), is `Abstract.wasmHOpenXP`, so
  `cfgEvFunXP = Shape.close cfgHOpenXP` is `Abstract.wasmEvFunXP`. The proof uses the machine
  theorems as for `cfgHOpen_eq`, and the exact correspondence of session and canonical runs
  (`Abstract.evalLXPS_canonical_cut`, `Abstract.evalLXPh_session_cut`).

* **`cfgEvInfN_eq`**, **`cfgEvFunD_eq`**, **`cfgEvFunDS_eq`**, **`cfgSessionTriple_eq`** (the
  session triple): the CFG triple `cfgSessionTriple`, whose divergent and productive parts run
  Wasm bodies on the logged machine (`LDLcfg` by `MachineL.MLogDivL`, `InfLcfg` by
  `MachineL.ProdL`), is `Abstract.sessionTripleXP`.
  * Productive streams: `MachineL.prodL_iff`, the session reading `OCall.toS` being injective,
    so `InfLcfg = Abstract.InfLwXP`.
  * Divergence after a log, at the level of `Shape.closeDLog` (not per call): `LDLwXP ⊆ LDLcfg`
    by `MachineL.logDiv_machine`; conversely `MachineL.machine_logDiv` extends the machine's log
    by canonical entries answered by the closed oracle (by values or an exception, never a trap),
    each resolving to the empty host log in `Shape.close wasmHOpenXP`
    (`Abstract.close_of_closedCallXP_vals`, `close_of_closedCallXP_throw`), so the host log of
    `closeDLog` is unchanged.
-/

namespace Silmaril.Wasm.Cfg.CfgSession

variable {H : Type}

/-- **The CFG open module is the session's open module.** -/
theorem cfgHOpen_eq :
    (cfgHOpenXPS : (Abstract.wasmHShapeS H).OpenMod) = Abstract.wasmHOpenXPS :=
  Proofs.CfgSession.cfgHOpen_eq

/-- **The CFG session closure is the store-retaining session closure.** -/
theorem cfgEvFun_eq :
    (cfgEvFunXPS : Silmaril.Games.Abstract.AFun (Abstract.wasmHostSig H) (Execution.Core.Store H)
      (Nat × List Execution.Core.Val) ((List Execution.Core.Val ⊕ Nat) ⊕ PUnit.{1})) =
      Abstract.wasmEvFunXPS :=
  Proofs.CfgSession.cfgEvFun_eq

/-- **The CFG session's pending host calls are the session's.** -/
theorem cfgPend_iff {s : Execution.Core.Store H} {a : Nat} {vs : List Execution.Core.Val}
    {q : List (Silmaril.Games.Abstract.Call (Abstract.wasmHostSig H))}
    {m : (Abstract.wasmHostSig H).Op} :
    CfgPendLXPS s a vs q m ↔ Abstract.PendLXPS s a vs q m :=
  Proofs.CfgSession.cfgPend_iff

/-- **The pending host calls of the CFG session are the session's.** -/
theorem cfgEvPend_eq :
    (cfgEvPendXPS : Silmaril.Games.Abstract.Pending (Abstract.wasmHostSig H)
      (Execution.Core.Store H) (Nat × List Execution.Core.Val)) = Abstract.wasmEvPendXPS :=
  Proofs.CfgSession.cfgEvPend_eq

/-- **The canonical CFG open module is the canonical open module.** For every function, store
and arguments, the trap-erasing module run on the logged machine (`cfgHOpenXP`, machine logs read
by `CanonRead`) has the behaviours of `Abstract.wasmHOpenXP`: finished Wasm bodies (their logs,
including a final callee-trap answer read as a cut call with every answer longer than the
callee's result arity, and their ends, a trap's store erased), pending tail calls with their
answers, and host calls. -/
theorem cfgHOpenX_eq :
    (cfgHOpenXP : (Abstract.wasmHShape H).OpenMod) = Abstract.wasmHOpenXP :=
  Proofs.CfgSession.cfgHOpenX_eq

/-- **The canonical CFG closure is the canonical closure**: `cfgEvFunXP`, which is
`Shape.close cfgHOpenXP`, is `Abstract.wasmEvFunXP`. -/
theorem cfgEvFunX_eq :
    (cfgEvFunXP : Silmaril.Games.Abstract.AFun (Abstract.wasmHostSig H) (Execution.Core.Store H)
      (Nat × List Execution.Core.Val) (List Execution.Core.Val ⊕ Nat)) = Abstract.wasmEvFunXP :=
  Proofs.CfgSession.cfgEvFunX_eq

/-- **The productive runs of the CFG closure are the canonical ones**: `cfgEvInfNXP`, the
productive closure of `cfgHOpenXP` with bodies run productively on the machine, is
`Abstract.wasmEvInfNXP`. -/
theorem cfgEvInfN_eq :
    (cfgEvInfNXP : Silmaril.Games.Abstract.PInf (Abstract.wasmHostSig H) (Execution.Core.Store H)
      (Nat × List Execution.Core.Val)) = Abstract.wasmEvInfNXP :=
  Proofs.CfgSession.cfgEvInfN_eq

/-- **The CFG closure with divergence is the canonical one**: `cfgEvFunDXP`, which is
`Shape.closeDLog cfgHOpenXP LDLcfg`, is `Abstract.wasmEvFunDXP`. -/
theorem cfgEvFunD_eq :
    (cfgEvFunDXP : Silmaril.Games.Abstract.AFun (Abstract.wasmHostSig H) (Execution.Core.Store H)
      (Nat × List Execution.Core.Val) (List Execution.Core.Val ⊕ Nat)) = Abstract.wasmEvFunDXP :=
  Proofs.CfgSession.cfgEvFunD_eq

/-- **The CFG session closure with divergence is the session's.** -/
theorem cfgEvFunDS_eq :
    (cfgEvFunDXPS : Silmaril.Games.Abstract.AFun (Abstract.wasmHostSig H)
      (Execution.Core.Store H) (Nat × List Execution.Core.Val)
      ((List Execution.Core.Val ⊕ Nat) ⊕ PUnit.{1})) = Abstract.wasmEvFunDXPS :=
  Proofs.CfgSession.cfgEvFunDS_eq

/-- **The CFG session triple is the session triple.** -/
theorem cfgSessionTriple_eq :
    (cfgSessionTriple : Silmaril.Games.Abstract.ObsTriple (Abstract.wasmHostSig H)
      (Execution.Core.Store H) (Nat × List Execution.Core.Val)
      ((List Execution.Core.Val ⊕ Nat) ⊕ PUnit.{1})) = Abstract.sessionTripleXP :=
  Proofs.CfgSession.cfgSessionTriple_eq

end Silmaril.Wasm.Cfg.CfgSession
