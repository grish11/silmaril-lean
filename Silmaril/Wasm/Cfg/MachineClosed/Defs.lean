module

public import Silmaril.Wasm.Abstract.Oracle.Thms
public import Silmaril.Wasm.Abstract.RegionCall.Defs

@[expose] public section

/-!
# The native slice of the checked closed oracle

`NativeCallOk s a us`: the guard under which the closed oracle is complete for Core calls
(`MachineClosed/Thms.lean`).
-/

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen

variable {H : Type}

/-- The guard of the native slice: a typed store, native Wasm functions, arity-checked
functions, and a typed invocation. -/
def NativeCallOk (s : Store H) (a : Nat) (us : List Val) : Prop :=
  StoreOk s ∧ NativeFuncsOk s.funcs ∧ Interp.StoreChk s.funcs ∧ InvokeOk s a us

end Silmaril.Wasm.Cfg.Machine
