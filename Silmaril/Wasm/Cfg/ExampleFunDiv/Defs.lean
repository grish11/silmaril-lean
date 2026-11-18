module

public import Silmaril.Wasm.Interp.ExampleX.Defs

/-!
# Function-level divergence through every call form: regression fixtures (definitions)

A validated module whose functions recurse through each call form, and two that trap:

```wat
(module
  (type (func))
  (table 1 funcref (ref.func 0))           ;; table 0: function 0
  (table 1 funcref (ref.null func))        ;; table 1: a null slot
  (global (ref null 0) (ref.func 1))       ;; global 0: function 1
  (global (ref null 0) (ref.null 0))       ;; global 1: null
  (func (type 0) (call_indirect 0 (type 0) (i32.const 0)))      ;; 0: itself, indirectly
  (func (type 0) (call_ref 0 (global.get 0)))                   ;; 1: itself, by reference
  (func (type 0) (return_call 2))                               ;; 2: itself, as a tail call
  (func (type 0) (return_call_indirect 1 (type 0) (i32.const 0))) ;; 3: a null slot: traps
  (func (type 0) (call_ref 0 (global.get 1))))                  ;; 4: a null reference: traps
```

The references come from globals: the native arity check (`Interp.tExt`) reads `global.get` but
not `ref.func`/`ref.null` in function bodies.

`fdMod` is the module, `fdPrep` its executable instantiation into the empty store (no imports,
no segments, no start function), `fdStore` the store it allocates.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.ExampleFunDiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp.ExampleX

/-- The example module. -/
def fdMod : Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  tables := [⟨⟨.i32, ⟨1, some 1⟩, funcref⟩, [.refFunc ⟨0⟩]⟩,
    ⟨⟨.i32, ⟨1, some 1⟩, funcref⟩, [.refNull (.abstract .func)]⟩]
  globals := [⟨⟨.const, .ref ⟨true, .typeIdx ⟨0⟩⟩⟩, [.refFunc ⟨1⟩]⟩,
    ⟨⟨.const, .ref ⟨true, .typeIdx ⟨0⟩⟩⟩, [.refNull (.typeIdx ⟨0⟩)]⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 0, .callIndirect ⟨0⟩ ⟨0⟩]⟩,
    ⟨⟨0⟩, [], [.globalGet ⟨0⟩, .callRef ⟨0⟩]⟩,
    ⟨⟨0⟩, [], [.returnCall ⟨2⟩]⟩,
    ⟨⟨0⟩, [], [.intConst .i32 0, .returnCallIndirect ⟨1⟩ ⟨0⟩]⟩,
    ⟨⟨0⟩, [], [.globalGet ⟨1⟩, .callRef ⟨0⟩]⟩]

/-- The executable instantiation of `fdMod` into the empty store. -/
def fdPrep : Config Empty × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Empty) fdMod []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance of `fdMod`. -/
def fdStore : Store Empty := fdPrep.1.store

/-- The functions' bodies. -/
abbrev g0 : Func := ⟨⟨0⟩, [], [.intConst .i32 0, .callIndirect ⟨0⟩ ⟨0⟩]⟩
abbrev g1 : Func := ⟨⟨0⟩, [], [.globalGet ⟨0⟩, .callRef ⟨0⟩]⟩
abbrev g2 : Func := ⟨⟨0⟩, [], [.returnCall ⟨2⟩]⟩
abbrev g3 : Func := ⟨⟨0⟩, [], [.intConst .i32 0, .returnCallIndirect ⟨1⟩ ⟨0⟩]⟩
abbrev g4 : Func := ⟨⟨0⟩, [], [.globalGet ⟨1⟩, .callRef ⟨0⟩]⟩

end Silmaril.Wasm.Cfg.ExampleFunDiv
