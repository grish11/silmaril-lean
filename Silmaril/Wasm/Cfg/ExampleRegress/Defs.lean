module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Game.Instance.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.ConstEval

/-!
# Regression fixtures for the self-contained CFG closure: recursion through a host, trap then
resume, productive host interaction (definitions)

One validated module with one imported host function `h : [i32] → []`, one mutable `i32`
global, and four functions, each exercising a different part of the CFG closure
`CfgClosure.cfgSessionTripleC`:

```wat
(module
  (type (func (param i32)))                 ;; 0
  (type (func))                             ;; 1
  (type (func (result i32)))                ;; 2
  (import "env" "h" (func (type 0)))        ;; function 0: the host
  (global (mut i32) (i32.const 0))          ;; global 0
  (func (type 0)                            ;; function 1, `rec n`
    local.get 0  call 0                     ;;   h(n), at every depth
    local.get 0
    if  local.get 0 i32.const 1 i32.sub call 1  end)  ;; rec(n - 1) when n ≠ 0
  (func (type 1)                            ;; function 2, `trap`
    i32.const 42  global.set 0  unreachable)
  (func (type 2)                            ;; function 3, `get`
    global.get 0)
  (func (type 1) (local i32)                ;; function 4, `pump`
    loop  local.get 0  call 0               ;;   h(k), forever
          local.get 0 i32.const 1 i32.add local.set 0  br 0  end)
  (export "rec" (func 1)) (export "trap" (func 2)) (export "get" (func 3))
  (export "pump" (func 4)))
```

* `rgMod`, `rgMT` (its validated type), `rgPrep` (the executable instantiation `prepare?`
  against one fresh host function, `Game.importStore`), `rgStore` (the store it allocates: the
  host function at address `0`, functions `1`–`4` at addresses `1`–`4`, the module's global at
  address `1`), `rgMI` (the functions' module instance), `rgI` (the scalar instance), `rgC₀`
  (the configuration of `$instantiate`).
* `rgStore42`: `rgStore` with the module's global set to `42`, the store `trap` leaves.
* `hostAt s n`: the host call `h(n)` in the store `s`, answered by no values and the same store
  (one host answer among all the session allows).
* `recLog s k`: the host calls of `rec k`, `h(k), h(k - 1), …, h(0)`, one per recursion depth.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.ExampleRegress

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Validation
open Silmaril.Games.Abstract (Call)

/-- Label `0`. -/
def l0 : LabelIdx := ⟨0, by decide⟩

/-- Local `0`. -/
def x0 : LocalIdx := ⟨0, by decide⟩

/-- `rec n`: `local.get 0; call 0; local.get 0; if (local.get 0; i32.const 1; i32.sub; call 1)`.
The host call `h(n)`, then the recursive call `rec(n - 1)` when `n ≠ 0`. -/
def recBody : Expr :=
  [.localGet x0, .call ⟨0⟩, .localGet x0,
    .if_ .empty [.localGet x0, .intConst .i32 1, .intBinOp .i32 .sub, .call ⟨1⟩] []]

/-- `trap`: `i32.const 42; global.set 0; unreachable`. -/
def trapBody : Expr := [.intConst .i32 42, .globalSet ⟨0⟩, .unreachable]

/-- `get`: `global.get 0`. -/
def getBody : Expr := [.globalGet ⟨0⟩]

/-- `pump`: `loop (local.get 0; call 0; local.get 0; i32.const 1; i32.add; local.set 0; br 0)`.
The host call `h(k)` on the counter `k`, forever. -/
def pumpBody : Expr :=
  [.loop .empty [.localGet x0, .call ⟨0⟩, .localGet x0, .intConst .i32 1, .intBinOp .i32 .add,
    .localSet x0, .br l0]]

/-- The module. -/
def rgMod : Module where
  types := [⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  imports := [⟨"env", "h", .func ⟨0⟩⟩]
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [⟨⟨0⟩, [], recBody⟩, ⟨⟨1⟩, [], trapBody⟩, ⟨⟨2⟩, [], getBody⟩, ⟨⟨1⟩, [.i32], pumpBody⟩]
  exports := [⟨"rec", .func ⟨1⟩⟩, ⟨"trap", .func ⟨2⟩⟩, ⟨"get", .func ⟨3⟩⟩, ⟨"pump", .func ⟨4⟩⟩]

/-- The validated type of `rgMod`. -/
def rgMT : CModuleType := (validate? rgMod).getD ⟨[], []⟩

/-- The executable instantiation of `rgMod` against one fresh host function. -/
def rgPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? (importStore (CExternType.funcs rgMT.imports)) rgMod
    (importAddrs rgMT)).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance: the host function at address `0`, `rec`, `trap`, `get`, `pump` at
addresses `1`–`4`. -/
def rgStore : Store Nat := rgPrep.1.store

/-- The configuration of `$instantiate` (no segments, no start function). -/
def rgC₀ : Config Nat := rgPrep.1.withStart rgPrep.2

/-- The scalar instance: the import `[i32] → []`, the exports `rec`, `trap`, `get`, `pump`. -/
def rgI : ScalarInstance where
  imports := [⟨[.num (.int .i32)], []⟩]
  exports := [⟨[.num (.int .i32)], []⟩, ⟨[], []⟩, ⟨[], [.num (.int .i32)]⟩, ⟨[], []⟩]
  addrs := exportFuncAddrs rgPrep.1.frame.module
  store := rgStore

/-- The module instance of the functions. -/
def rgMI : ModuleInst := rgPrep.1.frame.module

/-- The store `trap` leaves:the module's global (address `1`) set to `42`. -/
def rgStore42 : Store Nat := rgStore.setGlobal 1 (.i32 42)

/-- **The host call `h(n)` in the store `s`**, answered by no values in the same store. -/
abbrev hostAt (s : Store Nat) (n : BitVec 32) : Call (Abstract.wasmHostSig Nat) :=
  ⟨(0, s, [.i32 n]), (s, .values [])⟩

/-- **The host calls of `rec k`**: `h(k), h(k - 1), …, h(0)`, the call at depth `d` being
`h(k - d)`. -/
def recLog (s : Store Nat) : Nat → List (Call (Abstract.wasmHostSig Nat))
  | 0 => [hostAt s 0]
  | k + 1 => hostAt s (BitVec.ofNat 32 (k + 1)) :: recLog s k

end Silmaril.Wasm.Cfg.ExampleRegress
