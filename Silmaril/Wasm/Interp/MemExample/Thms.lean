module

public import Silmaril.Wasm.Interp.MemExample.Defs
public import Silmaril.Wasm.Interp.Thms
import Silmaril.Proofs.Wasm.Interp.MemExample

/-!
# A module with memory for native adequacy: theorems

Non-vacuity of native adequacy with memory instructions in the native profile.
`memMod` declares a memory with 0 pages; `f` stores and loads, `g` loads.

* `mem_instantiate`: `prepare?` of `memMod` is its Core 3.0 instantiation, at
  every profile and host.
* `mem_storeOk`, `mem_nativeFuncsOk`, `mem_storeChk`, `mem_invokeOk`: every
  hypothesis of `native_adequacy` holds.
* `mem_behaviours_f`, `mem_behaviours_g`: the Core 3.0 behaviours at every
  profile are exactly `traps`. `f(7)`'s `i32.store` and `g(0)`'s `i32.load` are
  out of bounds. This is computed by the native interpreter and transferred by
  adequacy, so the trap is Core's `store-num-oob`/`load-num-oob`.

A non-empty memory makes the kernel evaluate 64 KiB of bytes, which times out
under `decide +kernel`, so in-bounds runs are not exercised by an example
here. Their Core agreement, store update included, is the general
`steps_mem_normal`, used by `native_store_adequacy`.
-/

public section

namespace Silmaril.Wasm.Interp.MemExample

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp

theorem mem_instantiate (P : Numerics.Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) memMod [] memPrep.1 :=
  Silmaril.Proofs.Wasm.Interp.MemExample.mem_instantiate P host

theorem mem_storeOk : StoreOk memStore := Silmaril.Proofs.Wasm.Interp.MemExample.memStore_ok

theorem mem_nativeFuncsOk : Binaryen.NativeFuncsOk memStore.funcs :=
  nativeFuncsOk_of_check Silmaril.Proofs.Wasm.Interp.MemExample.memStore_native

theorem mem_storeChk : StoreChk memStore.funcs :=
  storeChk_of_check Silmaril.Proofs.Wasm.Interp.MemExample.memStore_chk

theorem mem_invokeOk (a : Nat) (ha : a < 2) (x : BitVec 32) : InvokeOk memStore a [Val.i32 x] :=
  Silmaril.Proofs.Wasm.Interp.MemExample.mem_invokeOk a ha x

/-- **`f(7)` traps in Core 3.0** at every profile (its store is out of bounds). -/
theorem mem_behaviours_f (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost memStore 0 [Val.i32 7] = {.traps} := by
  rw [native_adequacy mem_storeOk mem_nativeFuncsOk mem_storeChk (mem_invokeOk 0 (by omega) 7)]
  exact Silmaril.Proofs.Wasm.Interp.Example.nbeh_eq_singleton
    Silmaril.Proofs.Wasm.Interp.MemExample.memRun_f

/-- **`g(0)` traps in Core 3.0** at every profile (its load is out of bounds). -/
theorem mem_behaviours_g (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost memStore 1 [Val.i32 0] = {.traps} := by
  rw [native_adequacy mem_storeOk mem_nativeFuncsOk mem_storeChk (mem_invokeOk 1 (by omega) 0)]
  exact Silmaril.Proofs.Wasm.Interp.Example.nbeh_eq_singleton
    Silmaril.Proofs.Wasm.Interp.MemExample.memRun_g

end Silmaril.Wasm.Interp.MemExample
