module

public import Silmaril.Wasm.Interp.ExampleX.Defs

/-!
# A store whose functions make tail calls

Non-vacuity example for the tail call forms (`Silmaril.Wasm.Interp.OracleX`, checker `tExt`):

```wat
(module
  (type (func (result i32)))
  (table 1 funcref (ref.func 1))
  (table 1 funcref (ref.null func))
  (func (type 0) (return_call_indirect 0 (type 0) (i32.const 0)))  ;; slot 0 holds function 1
  (func (type 0) (i32.const 42))
  (func (type 0) (return_call_indirect 1 (type 0) (i32.const 0)))  ;; a null slot
  (func (type 0) (return_call 1)))
```

Function `0` tail-calls function `1` through table `0`; function `2` tail-calls through a null
slot of table `1`, which in Core 3.0 reaches `return_call_ref` on `ref.null` and traps only when
the frame is left; function `3` tail-calls function `1` directly.

* `tMod`: the module; `tPrep`: its executable instantiation into the empty store (no imports,
  no segments, no start function); `tStore`: the store it allocates.

Theorems in `Silmaril.Wasm.Interp.ExampleT.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp.ExampleT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp.ExampleX

/-- The example module. -/
def tMod : Module where
  types := [⟨[⟨true, [], .func ⟨[], [i32]⟩⟩]⟩]
  tables := [⟨⟨.i32, ⟨1, some 1⟩, funcref⟩, [.refFunc ⟨1⟩]⟩,
    ⟨⟨.i32, ⟨1, some 1⟩, funcref⟩, [.refNull (.abstract .func)]⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 0, .returnCallIndirect ⟨0⟩ ⟨0⟩]⟩,
    ⟨⟨0⟩, [], [.intConst .i32 42]⟩,
    ⟨⟨0⟩, [], [.intConst .i32 0, .returnCallIndirect ⟨1⟩ ⟨0⟩]⟩,
    ⟨⟨0⟩, [], [.returnCall ⟨1⟩]⟩]

/-- The spec's allocation of `tMod` into the empty store. -/
def tPrep : Config Empty × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Empty) tMod []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance of `tMod`. -/
def tStore : Store Empty := tPrep.1.store

end Silmaril.Wasm.Interp.ExampleT
