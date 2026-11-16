module

public import Silmaril.Wasm.Interp.ExampleT.Defs
public import Silmaril.Proofs.Wasm.Interp.ExampleT

/-!
# A store whose functions make tail calls: theorems

Non-vacuity of the tail call forms' Core 3.0 adequacy, on a concrete instantiated store:

* `tStore_ok`: the store is typed (from its validated instantiation);
* `tStore_chkE`: it passes the tail store check `StoreChkE tExt`; `tStore_not_native`,
  `tStore_not_ir`: it fails the native and the `irExt` checks, which reject tail calls;
* `tStore_good`: it is a good store for the closure's soundness;
* `t_indirect`, `t_null`, `t_direct`: the closed extended runs of functions `0` (a resolved
  `return_call_indirect` into function `1`, returning `42`), `2` (a `return_call_indirect`
  through a null table slot, a trap) and `3` (a `return_call` into function `1`);
* **`t_invoke`**, **`t_invoke_null`**, **`t_invoke_direct`**: their Core 3.0 invocations, at
  every profile, through `oracleSoundT_closedX`. The null tail call traps only once the frame
  is left (`return_call_ref` on `ref.null`, the pending null tail of `Outcome.tailNull`).
-/

public section

namespace Silmaril.Wasm.Interp.ExampleT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp

theorem tStore_ok : StoreOk tStore := Silmaril.Proofs.Wasm.Interp.ExampleT.tStore_ok

theorem tStore_chkE : StoreChkE tExt tStore.funcs := Silmaril.Proofs.Wasm.Interp.ExampleT.tStore_chkE

theorem tStore_not_native : storeChkB tStore.funcs = false :=
  Silmaril.Proofs.Wasm.Interp.ExampleT.tStore_not_chkB

theorem tStore_not_ir : ExampleX.storeChkEB irExt tStore.funcs = false :=
  Silmaril.Proofs.Wasm.Interp.ExampleT.tStore_not_irB

theorem tStore_good : GoodStoreX tStore := Silmaril.Proofs.Wasm.Interp.ExampleT.tStore_good

theorem t_indirect :
    Abstract.XRecursion.closedCallX tStore 0 [] (tStore, .ret [Val.i32 42]) :=
  Silmaril.Proofs.Wasm.Interp.ExampleT.t_indirect

theorem t_null : Abstract.XRecursion.closedCallX tStore 2 [] (tStore, .trap) :=
  Silmaril.Proofs.Wasm.Interp.ExampleT.t_null

theorem t_direct :
    Abstract.XRecursion.closedCallX tStore 3 [] (tStore, .ret [Val.i32 42]) :=
  Silmaril.Proofs.Wasm.Interp.ExampleT.t_direct

/-- **End to end, a resolved indirect tail call**: invoking function `0` returns `42`. -/
theorem t_invoke (P : Numerics.Profile) :
    Steps P noHostX (invoke tStore 0 []) ⟨tStore, {}, vals [Val.i32 42]⟩ :=
  Silmaril.Proofs.Wasm.Interp.ExampleT.t_invoke P

/-- **End to end, a null tail call**: invoking function `2` traps. -/
theorem t_invoke_null (P : Numerics.Profile) :
    Steps P noHostX (invoke tStore 2 []) ⟨tStore, {}, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Interp.ExampleT.t_invoke_null P

/-- **End to end, a direct tail call**: invoking function `3` returns `42`. -/
theorem t_invoke_direct (P : Numerics.Profile) :
    Steps P noHostX (invoke tStore 3 []) ⟨tStore, {}, vals [Val.i32 42]⟩ :=
  Silmaril.Proofs.Wasm.Interp.ExampleT.t_invoke_direct P

end Silmaril.Wasm.Interp.ExampleT
