module

public import Silmaril.Wasm.Cfg.BridgeCfg.Thms
public import Silmaril.Wasm.Interp.XProgress.Thms

@[expose] public section

/-!
# A defined function's CFG execution against its Core invocation (definitions)

`calleeDivX o`: the callees the function-level divergence results name as diverging. A callee
`a` on arguments `us` is a typed invocation of a `tExt`-checked store of Wasm functions with
function types, and its Core 3.0 invocation diverges at the deterministic profile `profile o`,
with no host.
-/

namespace Silmaril.Wasm.Cfg.Function

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp

variable {H : Type}

/-- **Diverging callees on the stated fragment**: a typed invocation of a `tExt`-checked store
of Wasm functions with function types, which diverges in Core 3.0 (profile `o`, no host). -/
def calleeDivX (o : SingleThreaded.GrowOracle) (s : Store H) (a : Nat) (us : List Val) : Prop :=
  StoreOk s ∧ InvokeOk s a us ∧ StoreChkE tExt s.funcs ∧ WasmFuncsT s ∧
    Diverges (SingleThreaded.profile o) noHostX (invoke s a us)

end Silmaril.Wasm.Cfg.Function
