module

public import Silmaril.Wasm.Interp.OracleX.Thms

@[expose] public section

/-!
# The typed closed extended oracle, for the block-CFG machine

`closedXOk`: answers of the closure of the extended call relation (`XRecursion.closedCallX`,
every call form in callee bodies), restricted to typed calls (`Interp.CX`: the callee's body is
typed in its call frame) on stores whose functions pass the tail-aware extended check
(`Interp.StoreChkE Interp.tExt`). The guard is part of the oracle relation, as in
`Abstract.closedCallOk`: soundness (`MachineClosedX/Thms.lean`) needs no further premise, and a
completeness statement has to discharge it at each call.
-/

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The typed closed extended oracle on `tExt`-checked stores. -/
def closedXOk : Abstract.CallRel H := fun s a us out =>
  Interp.StoreChkE Interp.tExt s.funcs ∧
    Interp.CX (Abstract.XRecursion.closedCallX : Abstract.CallRel H) s a us out

end Silmaril.Wasm.Cfg.Machine
