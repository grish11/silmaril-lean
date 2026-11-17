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

Not yet here: the CFG versions of the session triple's divergent and productive parts
(`sessionTripleXP`), via `MachineL.div_iff`/`logDiv_machine`/`machine_logDiv` and
`MachineL.prodL_iff` (`docs/projects/wasm-cfg.md`).
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

end Silmaril.Wasm.Cfg.CfgSession
