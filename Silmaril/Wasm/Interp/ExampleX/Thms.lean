module

public import Silmaril.Wasm.Interp.ExampleX.Defs
public import Silmaril.Proofs.Wasm.Interp.ExampleX

/-!
# A store whose function makes an indirect call: theorems

Non-vacuity of the extended call forms' Core 3.0 adequacy, on a concrete instantiated store
whose function `0` makes a `call_indirect` through the table into function `1`:

* `xStore_ok`: the store is typed (from its validated instantiation);
* `xStore_chkE`: it passes the extended store check `StoreChkE irExt`, and
  `xStore_not_native`: it fails the native one, so no native-profile gate is hiding;
* `xStore_good`: it is a good store for the closure's soundness;
* `x_caller`: the closed extended semantics runs function `0` to `42` (the indirect call
  resolves table slot `0` to function `1`, whose cast to the annotated type succeeds);
* **`x_invoke`**: Core 3.0 invocation of function `0` returns `42`, at every profile, derived
  from the closed extended semantics through `oracleSoundX_closedX`.
-/

public section

namespace Silmaril.Wasm.Interp.ExampleX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp

theorem xStore_ok : StoreOk xStore := Silmaril.Proofs.Wasm.Interp.ExampleX.xStore_ok

theorem xStore_chkE : StoreChkE irExt xStore.funcs :=
  Silmaril.Proofs.Wasm.Interp.ExampleX.storeChkE_of_storeChkEB
    Silmaril.Proofs.Wasm.Interp.ExampleX.xStore_chkEB

theorem xStore_not_native : storeChkB xStore.funcs = false :=
  Silmaril.Proofs.Wasm.Interp.ExampleX.xStore_not_chkB

theorem xStore_good : GoodStoreX xStore := Silmaril.Proofs.Wasm.Interp.ExampleX.xStore_good

theorem x_caller :
    Abstract.XRecursion.closedCallX xStore 0 [] (xStore, .normal [Val.i32 42]) :=
  Silmaril.Proofs.Wasm.Interp.ExampleX.x_caller

/-- **End to end, in Core 3.0**: invoking function `0`, which makes an indirect call, returns
`42`. -/
theorem x_invoke (P : Numerics.Profile) :
    Steps P noHostX (invoke xStore 0 []) ⟨xStore, {}, vals [Val.i32 42]⟩ :=
  Silmaril.Proofs.Wasm.Interp.ExampleX.x_invoke P

end Silmaril.Wasm.Interp.ExampleX
