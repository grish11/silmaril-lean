module

public import Silmaril.Wasm.Abstract.Recursion.Defs
public import Silmaril.Wasm.Interp.Defs

/-!
# The closed oracle for Region calls

`closedCallOk` is `closedCall` restricted to the stores and invocations on which
native evaluation is known to be a Core 3.0 run: arity-checked stores
(`Interp.StoreChk`) and typed invocations (`InvokeOk`). `Region.CallSound`
quantifies over every store, and soundness of native evaluation is only proved
on those, so the unrestricted `closedCall` is not claimed sound. Theorems:
`Silmaril.Wasm.Abstract.RegionCall.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The closed oracle on arity-checked stores and typed invocations. -/
def closedCallOk : CallRel H := fun s a us out =>
  closedCall s a us out ∧ Silmaril.Wasm.Interp.StoreChk s.funcs ∧ InvokeOk s a us

end Silmaril.Wasm.Abstract
