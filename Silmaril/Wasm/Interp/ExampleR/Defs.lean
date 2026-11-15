module

public import Silmaril.Wasm.Interp.ExampleX.Defs

/-!
# A store whose function makes a reference call

Non-vacuity example for `call_ref` through the **typed** route (`OracleX`), where the call's
arity premise is discharged from the Core typing of the call site, not from a cast:

```wat
(module
  (type (func (result i32)))
  (type (func (param (ref null 0)) (result i32)))
  (func (type 1) (call_ref 0 (local.get 0)))  ;; calls its function-reference argument
  (func (type 0) (i32.const 42)))
```

Function `0` is invoked on `ref.func 1`. A `call_ref` in a store function is outside the
good-store closure (`GoodStoreX` excludes it), so only the typed closure covers it.

Theorems in `Silmaril.Wasm.Interp.ExampleR.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp.ExampleR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp.ExampleX

/-- The example module. -/
def rMod : Module where
  types := [⟨[⟨true, [], .func ⟨[], [i32]⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[.ref ⟨true, .typeIdx ⟨0⟩⟩], [i32]⟩⟩]⟩]
  funcs := [⟨⟨1⟩, [], [.localGet ⟨0⟩, .callRef ⟨0⟩]⟩, ⟨⟨0⟩, [], [.intConst .i32 42]⟩]

/-- The spec's allocation of `rMod` into the empty store. -/
def rPrep : Config Empty × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Empty) rMod []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance of `rMod`. -/
def rStore : Store Empty := rPrep.1.store

end Silmaril.Wasm.Interp.ExampleR
