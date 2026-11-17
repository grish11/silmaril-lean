module

public import Silmaril.Wasm.Cfg.Session.Defs
public import Silmaril.Wasm.Interp.ExampleX.Defs
public import Silmaril.Wasm.Component.DWiring.Defs

/-!
# Checking the CFG session's domain (definitions)

The CFG session (`Silmaril.Wasm.Cfg.Session`) is the instance session exactly on its domain
`HFOk I s`. This module gives an executable check of that domain for an instantiated module,
built from existing checkers, and the domain of a component.

* `wasmFuncsB F`: every function of `F` is a Wasm function whose type is a function type (the
  executable `WasmFuncsT`).
* `exportsB I`: one address per export, and the function at each export address has the
  export's type (`expand?`, the executable `Expand`).
* `hfCheck I`: no imports, the tail-aware arity check `Interp.ExampleX.storeChkEB Interp.tExt`
  (the executable `StoreChkE tExt`), `wasmFuncsB` and `exportsB`, at the instance's store.
  With a validated module whose instantiation into the empty store gives that store, it gives
  `HFOk I I.store` (`SessionCheck.hfOk_of_check`): store typing comes from instantiation, not
  from the check.
* `NodesIn p`, `NodeIn p`, `CompIn p`: every core instance of a component (nested components
  included) satisfies `p`. The component-level CFG theorems are stated on
  `CompIn (fun m => HFOk m.inst m.inst.store)`, not by a fallback.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.SessionCheck

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp
open Silmaril.Wasm.Component

/-- **Every function is a Wasm function with a function type** (executable `WasmFuncsT`). -/
def wasmFuncsB {H : Type} (F : List (FuncInst H)) : Bool :=
  F.all fun fi => match fi.code with
    | .wasm _ => (Validation.DefType.funcType? fi.type).isSome
    | .host _ => false

/-- **The exports have their types**: one address per export, and the function at each export
address expands to the export's type. -/
def exportsB (I : ScalarInstance) : Bool :=
  I.addrs.length == I.exports.length &&
    (List.finRange I.exports.length).all fun j =>
      match I.store.funcs[I.addr j]? with
      | some fi => decide (fi.type.expand? = some (I.exports.get j).toComp)
      | none => false

/-- **The executable check of the CFG session's domain** at the instance's store. -/
def hfCheck (I : ScalarInstance) : Bool :=
  I.imports.isEmpty && ExampleX.storeChkEB tExt I.store.funcs && wasmFuncsB I.store.funcs &&
    exportsB I

variable {M : Type}

mutual
/-- Every core instance of the node satisfies `p`. -/
def NodeIn (p : M → Prop) : Node M → Prop
  | .core m _ => p m
  | .inst c _ => CompIn p c

/-- **Every core instance of the component satisfies `p`**, nested components included. -/
def CompIn (p : M → Prop) : Comp M → Prop
  | .mk _ ns _ => NodesIn p ns

/-- Every core instance of the nodes satisfies `p`. -/
def NodesIn (p : M → Prop) : List (Node M) → Prop
  | [] => True
  | n :: ns => NodeIn p n ∧ NodesIn p ns
end

end Silmaril.Wasm.Cfg.SessionCheck
