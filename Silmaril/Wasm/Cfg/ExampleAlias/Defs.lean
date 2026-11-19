module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Game.Instance.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.ConstEval

/-!
# A validated aliasing cycle through a dangling host exception (definitions)

One validated module with one tag `$t : [exnref]` and one imported host function `h : [] → []`:
```wat
(module
  (type (func (param exnref)))              ;; 0: the tag's type
  (type (func))                             ;; 1
  (type (func (result exnref)))             ;; 2
  (import "env" "h" (func (type 1)))        ;; function 0: the host
  (tag (type 0))                            ;; tag 0, `$t`
  (func (type 1)                            ;; function 1, `run`
    call 2  throw 0)
  (func (type 2)                            ;; function 2, `grab`
    try_table (result exnref) (catch_all_ref 0)  call 0  unreachable  end)
  (export "run" (func 1)))
```
`grab` calls `h` under `catch_all_ref 0`, which branches to the function label with the caught
reference; `run` throws that reference as the payload of `$t`. When `h` throws the dangling
address `0` (the store has no exception), `grab` returns `ref.exn 0` and `throw 0` allocates the
exception `⟨0, [ref.exn 0]⟩` at address `0`: it refers to itself.

A second module, `dcMod`, is a validated module accepted by the exception checker whose function
holds an unsupported instruction in dead code:
```wat
(module (type (func)) (func (type 0) unreachable  ref.test anyref  drop) (export "dead" (func 0)))
```

* `alMod`, `alMT`, `alPrep`, `alStore` (the host function at address `0`, `run` at `1`, `grab` at
  `2`, the tag at `0`, no exceptions), `alMI`, `alI`, `alC₀`, as in `ExampleHostExn`; `alFr`, the
  frame of a call to `run` or `grab`;
* `alCyc`: the exception `⟨0, [ref.exn 0]⟩`; `alEnd`: `alStore` with it allocated at address `0`;
* `alAns`: the host call `h()` in `alStore` answered by `throw 0`, the store unchanged;
* `dcMod`, `dcMT`, `dcPrep`, `dcStore`, `dcI`, `dcC₀`.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.ExampleAlias

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Validation
open Silmaril.Games.Abstract (Call)

/-- Label `0`. -/
def l0 : LabelIdx := ⟨0, by decide⟩

/-- The value type `exnref`. -/
def exnRef : ValType := .ref ⟨true, .abstract .exn⟩

/-- `run`: `call 2; throw 0`. -/
def runBody : Expr := [.call ⟨2⟩, .throw ⟨0⟩]

/-- `grab`: `try_table (result exnref) (catch_all_ref 0) (call 0; unreachable)`. -/
def grabBody : Expr := [.tryTable (.value exnRef) [.catchAllRef l0] [.call ⟨0⟩, .unreachable]]

/-- The module. -/
def alMod : Module where
  types := [⟨[⟨true, [], .func ⟨[exnRef], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[], [exnRef]⟩⟩]⟩]
  imports := [⟨"env", "h", .func ⟨1⟩⟩]
  tags := [⟨0⟩]
  funcs := [⟨⟨1⟩, [], runBody⟩, ⟨⟨2⟩, [], grabBody⟩]
  exports := [⟨"run", .func ⟨1⟩⟩]

/-- The validated type of `alMod`. -/
def alMT : CModuleType := (validate? alMod).getD ⟨[], []⟩

/-- The executable instantiation of `alMod` against one fresh host function. -/
def alPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? (importStore (CExternType.funcs alMT.imports)) alMod
    (importAddrs alMT)).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance. -/
def alStore : Store Nat := alPrep.1.store

/-- The configuration of `$instantiate`. -/
def alC₀ : Config Nat := alPrep.1.withStart alPrep.2

/-- The scalar instance: the import `[] → []`, the export `run : [] → []`. -/
def alI : ScalarInstance where
  imports := [⟨[], []⟩]
  exports := [⟨[], []⟩]
  addrs := exportFuncAddrs alPrep.1.frame.module
  store := alStore

/-- The module instance of the functions. -/
def alMI : ModuleInst := alPrep.1.frame.module

/-- The frame of a call to `run` or `grab` (no arguments, no locals). -/
abbrev alFr : Frame := Frame.forCall alMI [] []

/-- The self-referencing exception of the tag at address `0`. -/
def alCyc : ExnInst := ⟨0, [.ref (.exn 0)]⟩

/-- `alStore` with `alCyc` allocated at address `0`. -/
def alEnd : Store Nat := alStore.addExn alCyc

/-- The host call `h()` in `alStore`, answered by the dangling exception `0`. -/
abbrev alAns : Call (Abstract.wasmHostSig Nat) := ⟨(0, alStore, []), (alStore, .throw 0)⟩

/-- `dead`: `unreachable; ref.test anyref; drop`. -/
def deadBody : Expr := [.unreachable, .refTest ⟨true, .abstract .any⟩, .drop]

/-- The dead-code module. -/
def dcMod : Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], deadBody⟩]
  exports := [⟨"dead", .func ⟨0⟩⟩]

/-- The validated type of `dcMod`. -/
def dcMT : CModuleType := (validate? dcMod).getD ⟨[], []⟩

/-- The executable instantiation of `dcMod` (no imports). -/
def dcPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? (importStore (CExternType.funcs dcMT.imports)) dcMod
    (importAddrs dcMT)).getD (⟨{}, {}, []⟩, none)

/-- The store of the dead-code instance. -/
def dcStore : Store Nat := dcPrep.1.store

/-- The configuration of its `$instantiate`. -/
def dcC₀ : Config Nat := dcPrep.1.withStart dcPrep.2

/-- The dead-code scalar instance: no import, the export `dead : [] → []`. -/
def dcI : ScalarInstance where
  imports := []
  exports := [⟨[], []⟩]
  addrs := exportFuncAddrs dcPrep.1.frame.module
  store := dcStore

end Silmaril.Wasm.Cfg.ExampleAlias
