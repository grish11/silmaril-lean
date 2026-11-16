module

public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# A store whose function makes an indirect call

Non-vacuity example for the extended call forms (`Silmaril.Wasm.Interp.OracleX`):

```wat
(module
  (type (func (result i32)))
  (table 1 funcref (ref.func 1))
  (func (type 0) (call_indirect 0 (type 0) (i32.const 0)))  ;; calls the table's slot 0
  (func (type 0) (i32.const 42)))
```

The indirect call is inside a *store function*, so the example exercises the extended
store check `StoreChkE irExt` (not the native one, which rejects it).

* `xMod`: the module (silmaril-lean's Core `Module`);
* `xPrep`: its executable instantiation `prepare?` into the empty store (no imports, no
  segments, no start function; the table is filled by its initializer);
* `xStore`: the store it allocates (Wasm functions at addresses `0` and `1`, one table).

Theorems in `Silmaril.Wasm.Interp.ExampleX.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp.ExampleX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- `i32`. -/
abbrev i32 : ValType := .num (.int .i32)

/-- `funcref`. -/
abbrev funcref : RefType := ⟨true, .abstract .func⟩

/-- The example module. -/
def xMod : Module where
  types := [⟨[⟨true, [], .func ⟨[], [i32]⟩⟩]⟩]
  tables := [⟨⟨.i32, ⟨1, some 1⟩, funcref⟩, [.refFunc ⟨1⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 0, .callIndirect ⟨0⟩ ⟨0⟩]⟩, ⟨⟨0⟩, [], [.intConst .i32 42]⟩]

/-- The spec's allocation of `xMod` into the empty store. -/
def xPrep : Config Empty × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Empty) xMod []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance of `xMod`. -/
def xStore : Store Empty := xPrep.1.store

/-- An executable `StoreChkE ext` for one function (host functions and functions without
a function type pass vacuously). -/
def funcChkEB {H : Type} (ext : ExtArity H) (F : List (FuncInst H)) (fi : FuncInst H) : Bool :=
  match fi.code, Validation.DefType.funcType? fi.type with
  | .wasm fn, some (ps, rs) =>
    endsAt (chkE ext F fi.module (ps.length + fn.locals.length) rs.length [rs.length] (some 0)
      (Binaryen.liftInstrs fn.body)) rs.length
  | _, _ => true

/-- **An executable `StoreChkE ext`.** -/
def storeChkEB {H : Type} (ext : ExtArity H) (F : List (FuncInst H)) : Bool :=
  F.all (funcChkEB ext F)

end Silmaril.Wasm.Interp.ExampleX
