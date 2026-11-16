module

public import Silmaril.Wasm.Interp.ExampleR.Defs
public import Silmaril.Proofs.Wasm.Interp.ExampleR

/-!
# A store whose function makes a reference call: theorems

Non-vacuity of the **typed** route for `call_ref`: a concrete instantiated store whose function
`0` makes a `call_ref` on its function-reference argument.

* `rStore_ok`: the store is typed; `rStore_chkE`: it passes `StoreChkE irExt`, and fails the
  native check (`rStore_not_native`);
* `rStore_not_good`: it is **outside** the good-store closure (`GoodStoreX` excludes
  `call_ref`), so only the typed closure covers it;
* **`r_invoke`**: Core 3.0 invocation of function `0` on `ref.func 1` returns `42`, at every
  profile, through `oracleSoundX_typedClosed`: the call's arity premise comes from the Core
  typing of the call site, the callee's entry from the typed invocation (`r_invokeOk`).
-/

public section

namespace Silmaril.Wasm.Interp.ExampleR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp

theorem rStore_ok : StoreOk rStore := Silmaril.Proofs.Wasm.Interp.ExampleR.rStore_ok

theorem rStore_chkE : StoreChkE irExt rStore.funcs := Silmaril.Proofs.Wasm.Interp.ExampleR.rStore_chkE

theorem rStore_not_native : storeChkB rStore.funcs = false :=
  Silmaril.Proofs.Wasm.Interp.ExampleR.rStore_not_chkB

theorem rStore_not_good : ¬ GoodStoreX rStore := Silmaril.Proofs.Wasm.Interp.ExampleR.rStore_not_good

theorem r_invokeOk : InvokeOk rStore 0 [.ref (.func 1)] :=
  Silmaril.Proofs.Wasm.Interp.ExampleR.r_invokeOk

/-- **End to end, in Core 3.0, through the typed route**: invoking function `0` on
`ref.func 1`, whose body makes a `call_ref`, returns `42`. -/
theorem r_invoke (P : Numerics.Profile) :
    Steps P noHostX (invoke rStore 0 [.ref (.func 1)]) ⟨rStore, {}, vals [Val.i32 42]⟩ :=
  Silmaril.Proofs.Wasm.Interp.ExampleR.r_invoke P

end Silmaril.Wasm.Interp.ExampleR
