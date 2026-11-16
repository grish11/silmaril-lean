module

public import Silmaril.Wasm.Abstract.Closing.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# Unbounded recursion: a function that only calls itself

`SelfLoop s a`: the function at address `a` is native code whose whole body
is `call x`, and `x` names `a` itself in its module. Its call recurses
forever. It is the concrete Wasm form of the recursion audit of
`Silmaril.Games.Abstract.Shape.close`:

* the least-fixpoint closing gives it **no behaviour**;
* `closeD` gives it exactly `div`, through the infinite internal-call chain;
* Core 3.0 diverges.

`recMod` is a validated module with one such function,

```wat
(module
  (type (func))
  (func (type 0) (call 0))
  (export "f" (func 0)))
```

and `recStore` is the store its executable instantiation allocates.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The function at `a` is native code whose body is `call x`, with `x` naming
`a` itself. -/
def SelfLoop (s : Store H) (a : Nat) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func) (x : FuncIdx) (ps rs : List Validation.CValType),
    s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧ fn.body = [.call x] ∧
    fi.module.funcs[x.toNat]? = some a ∧ Validation.DefType.funcType? fi.type = some (ps, rs)

/-- The executable check behind `SelfLoop`. -/
def selfLoopB (s : Store H) (a : Nat) : Bool :=
  match s.funcs[a]? with
  | some fi =>
    match fi.code with
    | .wasm fn =>
      match fn.body with
      | [.call x] => fi.module.funcs[x.toNat]? == some a &&
          (Validation.DefType.funcType? fi.type).isSome
      | _ => false
    | _ => false
  | none => false

/-- `(module (type (func)) (func (type 0) (call 0)) (export "f" (func 0)))`. -/
def recMod : Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.call ⟨0⟩]⟩]
  exports := [⟨"f", .func ⟨0⟩⟩]

/-- The executable instantiation of `recMod` into the empty store. -/
def recPrep : Config Empty × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Empty) recMod []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance of `recMod`. -/
def recStore : Store Empty := recPrep.1.store

end Silmaril.Wasm.Abstract
