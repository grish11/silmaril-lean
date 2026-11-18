module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Game.Instance.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.ConstEval

/-!
# Host exceptions and traps under `try_table`, on the self-contained CFG closure (definitions)

One validated module with one tag `$e : [i32]`, one imported host function `h : [] → [i32]`, and
three functions, each a `try_table` around a call to `h`:

```wat
(module
  (type (func (param i32)))                 ;; 0: the tag's type
  (type (func (result i32)))                ;; 1
  (type (func))                             ;; 2
  (import "env" "h" (func (type 1)))        ;; function 0: the host
  (tag (type 0))                            ;; tag 0, `$e`
  (func (type 1)                            ;; function 1, `callH`
    try_table (result i32) (catch 0 0)  call 0         end)
  (func (type 1)                            ;; function 2, `tailH`
    try_table (result i32) (catch 0 0)  return_call 0  end)
  (func (type 2)                            ;; function 3, `trapH`
    try_table (catch_all 0)  call 0  drop  end)
  (export "callH" (func 1)) (export "tailH" (func 2)) (export "trapH" (func 3)))
```

The clauses `catch 0 0` branch to the function label (`$e`'s payload is the function's result);
`catch_all 0` branches to the function label with no values.

* `hxMod`, `hxMT` (its validated type), `hxPrep` (the executable instantiation `prepare?`
  against one fresh host function, `Game.importStore`), `hxStore` (the store it allocates: the
  host function at address `0`, functions `1`–`3` at addresses `1`–`3`, the tag at address `0`,
  no exceptions), `hxMI` (the functions' module instance), `hxI` (the scalar instance), `hxC₀`
  (the configuration of `$instantiate`).
* `hxExn v`: the exception of the tag at address `0` carrying `v`; `hxThrown v`: `hxStore` with
  that exception allocated at address `0`, the store a host leaves when it allocates and throws
  it.
* `hostAns s r s'`: the host call `h()` in the store `s`, answered by the result `r` leaving `s'`.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.ExampleHostExn

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Validation
open Silmaril.Games.Abstract (Call)

/-- Label `0`. -/
def l0 : LabelIdx := ⟨0, by decide⟩

/-- The clause `catch 0 0`: tag `0`, to the label outside the `try_table`. -/
def catchE : Catch := .catch_ ⟨0⟩ l0

/-- `callH`: `try_table (result i32) (catch 0 0) (call 0)`. -/
def callBody : Expr := [.tryTable (.value .i32) [catchE] [.call ⟨0⟩]]

/-- `tailH`: `try_table (result i32) (catch 0 0) (return_call 0)`. -/
def tailBody : Expr := [.tryTable (.value .i32) [catchE] [.returnCall ⟨0⟩]]

/-- `trapH`: `try_table (catch_all 0) (call 0; drop)`. -/
def trapBody : Expr := [.tryTable .empty [.catchAll l0] [.call ⟨0⟩, .drop]]

/-- The module. -/
def hxMod : Module where
  types := [⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  imports := [⟨"env", "h", .func ⟨1⟩⟩]
  tags := [⟨0⟩]
  funcs := [⟨⟨1⟩, [], callBody⟩, ⟨⟨1⟩, [], tailBody⟩, ⟨⟨2⟩, [], trapBody⟩]
  exports := [⟨"callH", .func ⟨1⟩⟩, ⟨"tailH", .func ⟨2⟩⟩, ⟨"trapH", .func ⟨3⟩⟩]

/-- The validated type of `hxMod`. -/
def hxMT : CModuleType := (validate? hxMod).getD ⟨[], []⟩

/-- The executable instantiation of `hxMod` against one fresh host function. -/
def hxPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? (importStore (CExternType.funcs hxMT.imports)) hxMod
    (importAddrs hxMT)).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance: the host function at address `0`, `callH`, `tailH`, `trapH` at
addresses `1`–`3`, the tag at address `0`. -/
def hxStore : Store Nat := hxPrep.1.store

/-- The configuration of `$instantiate` (no segments, no start function). -/
def hxC₀ : Config Nat := hxPrep.1.withStart hxPrep.2

/-- The scalar instance: the import `[] → [i32]`, the exports `callH`, `tailH`, `trapH`. -/
def hxI : ScalarInstance where
  imports := [⟨[], [.num (.int .i32)]⟩]
  exports := [⟨[], [.num (.int .i32)]⟩, ⟨[], [.num (.int .i32)]⟩, ⟨[], []⟩]
  addrs := exportFuncAddrs hxPrep.1.frame.module
  store := hxStore

/-- The module instance of the functions. -/
def hxMI : ModuleInst := hxPrep.1.frame.module

/-- The exception of the tag at address `0` (the module's tag `$e`) carrying `v`. -/
def hxExn (v : BitVec 32) : ExnInst := ⟨0, [.i32 v]⟩

/-- `hxStore` with the exception `hxExn v` allocated at address `0`: the store a host leaves when
it allocates that exception and throws it. -/
def hxThrown (v : BitVec 32) : Store Nat := { hxStore with exns := [hxExn v] }

/-- **The host call `h()` in the store `s`**, answered by the result `r` leaving `s'`. -/
abbrev hostAns (s : Store Nat) (r : Result) (s' : Store Nat) : Call (Abstract.wasmHostSig Nat) :=
  ⟨(0, s, []), (s', r)⟩

end Silmaril.Wasm.Cfg.ExampleHostExn
