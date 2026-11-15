module

public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# A module with memory for native adequacy

```wat
(module
  (type (func (param i32) (result i32)))
  (memory 0)
  (func (type 0)                       ;; f: store the argument at 0, load it back
    (i32.store (i32.const 0) (local.get 0))
    (i32.load (i32.const 0)))
  (func (type 0)                       ;; g: load at the argument address
    (i32.load (local.get 0)))
  (export "f" (func 0)) (export "g" (func 1)))
```

`memMod`, its executable instantiation `memPrep` into the empty store, and the
store `memStore` it allocates. Theorems: `Silmaril.Wasm.Interp.MemExample.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp.MemExample

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- `i32`. -/
abbrev i32 : ValType := .num (.int .i32)

/-- `memarg` with alignment 2 and offset 0. -/
abbrev ma0 : MemArg := ⟨2, 0⟩

/-- The example module. -/
def memMod : Module where
  types := [⟨[⟨true, [], .func ⟨[i32], [i32]⟩⟩]⟩]
  memories := [⟨.i32, ⟨0, none⟩⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 0, .localGet ⟨0⟩, .intStore .i32 none ⟨0⟩ ma0,
      .intConst .i32 0, .intLoad .i32 none ⟨0⟩ ma0]⟩,
    ⟨⟨0⟩, [], [.localGet ⟨0⟩, .intLoad .i32 none ⟨0⟩ ma0]⟩]
  exports := [⟨"f", .func ⟨0⟩⟩, ⟨"g", .func ⟨1⟩⟩]

/-- The executable instantiation of `memMod` into the empty store. -/
def memPrep : Config Empty × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Empty) memMod []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance. -/
def memStore : Store Empty := memPrep.1.store

end Silmaril.Wasm.Interp.MemExample
