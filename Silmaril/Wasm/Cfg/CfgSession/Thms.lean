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

Not yet here: the CFG versions of the session triple's pending and divergent/productive parts
(`sessionTripleXP`), via `MachineL.pending_iff`, `MachineL.div_iff`/`logDiv_machine`/
`machine_logDiv` and `MachineL.prodL_iff` (`docs/projects/wasm-cfg.md`).
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

end Silmaril.Wasm.Cfg.CfgSession
