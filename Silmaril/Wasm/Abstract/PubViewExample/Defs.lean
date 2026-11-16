module

public import Silmaril.Wasm.Abstract.PubView.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# A store view that identifies an internal call with its inlining: definitions

Two modules with the same type, the same two function types and the same export `"f"` of
function `0`. They differ only in the body of function `0`:

```wat
(module                                  (module
  (type (func (result i32)))               (type (func (result i32)))
  (func (type 0) (call 1))                 (func (type 0) (i32.const 42))
  (func (type 0) (i32.const 42))           (func (type 0) (i32.const 42))
  (export "f" (func 0)))                   (export "f" (func 0)))
```

`callMod` (left) calls an internal helper. `inlineMod` (right) is the same module with the
call inlined; the helper stays in place, now dead, so that both stores have the same shape.
`callStore` and `inlineStore` are the stores that their executable instantiations (`prepare?`)
allocate into the empty store. The host function type is `Empty`, so neither store has a host
function. Each module exports the function at address `0`.

**The view.** `codeView s` keeps every field of the store except function code. Of each
function instance it keeps the type and the module instance. It keeps the tags, globals,
memories, tables, data and element instances, structs, arrays and exceptions unchanged. It
forgets function code because that is the only place where the two stores differ. Their module
instances, export names and function types agree; the export is named `"f"` in both modules for
that reason. Any view that keeps the code of function `0` separates the two stores. The identity
view gives `PubEquiv`, which distinguishes the two exports.

Theorems in `Silmaril.Wasm.Abstract.PubViewExample.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.PubViewExample

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- `(type (func (result i32)))`. -/
def resI32 : RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩

/-- Function `0` calls the helper, function `1` returns `42`; function `0` is exported. -/
def callMod : Module where
  types := [resI32]
  funcs := [⟨⟨0⟩, [], [.call ⟨1⟩]⟩, ⟨⟨0⟩, [], [.intConst .i32 42]⟩]
  exports := [⟨"f", .func ⟨0⟩⟩]

/-- `callMod` with the call inlined: function `0` returns `42`; function `1` is unchanged. -/
def inlineMod : Module where
  types := [resI32]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 42]⟩, ⟨⟨0⟩, [], [.intConst .i32 42]⟩]
  exports := [⟨"f", .func ⟨0⟩⟩]

/-- The store of the executable instantiation of `m` into the empty store. -/
def prepStore (m : Module) : Store Empty :=
  ((prepare? evalConst? ({} : Store Empty) m []).getD (⟨{}, {}, []⟩, none)).1.store

/-- The store of the instance of `callMod`; its export `"f"` is at address `0`. -/
def callStore : Store Empty := prepStore callMod

/-- The store of the instance of `inlineMod`; its export `"f"` is at address `0`. -/
def inlineStore : Store Empty := prepStore inlineMod

/-- What `codeView` keeps of a store: all of it except function code. -/
structure CodeView where
  /-- The type and module instance of each function. -/
  funcs : List (Validation.DefType × ModuleInst)
  tags : List TagInst
  globals : List GlobalInst
  mems : List MemInst
  tables : List TableInst
  datas : List DataInst
  elems : List ElemInst
  structs : List StructInst
  arrays : List ArrayInst
  exns : List ExnInst
  deriving DecidableEq

/-- **The view that forgets function code.** -/
def codeView {H : Type} (s : Store H) : CodeView :=
  ⟨s.funcs.map fun fi => (fi.type, fi.module), s.tags, s.globals, s.mems, s.tables, s.datas,
    s.elems, s.structs, s.arrays, s.exns⟩

end Silmaril.Wasm.Abstract.PubViewExample
