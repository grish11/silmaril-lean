module

public import Silmaril.Wasm.Cfg.Machine.Defs
public import Silmaril.Wasm.Interp.ExampleX.Defs
public import Silmaril.Wasm.Execution.Core.Exec.ConstEval

/-!
# Leaving the function through a caught exception: regression fixtures (definitions)

The machine's exit by a caught exception branching to the function label (`MStepC.catchOut`)
carries the **whole frame stack**: the caught values over the `try_table`'s outer values, under
the outer values of every frame the branch leaves (`brVals`), as Core's `handler` and
branch-through-label rules unwind them. These bodies, of type `[] → [i32 i32]`, throw the tag
`0 : [i32 i32] → []` with the payload `3, 4` and catch it with `catch 0 l` to the function label
(a typed clause carries exactly the label's values, here the payload):

* `bodyCatch`: `i32.const 1; try_table (catch 0 0) (i32.const 3; i32.const 4; throw 0);
  unreachable`. Core returns `3, 4`; the machine exits with the whole stack `1, 3, 4`.
* `bodyCatchNest`: `i32.const 1; block (i32.const 2; try_table (catch 0 1) (…); drop);
  unreachable`. Core returns `3, 4`; the machine exits with the whole stack `1, 2, 3, 4`.

In both, the results are the top two values of the exit stack (`Session.sinkResult`); the values
below them are the outer values of the frames the branch leaves.

`catchStore` is the store the executable instantiation `catchPrep` allocates, `catchMI` the
functions' module instance: there the tag hypotheses of the fixtures hold (`catch_tag`).

(The `unreachable` after a construct that never falls through, and the `drop`, only make the
bodies valid.) `catchMod` declares the tag and validates.

These fixtures are about the exit state only. They are outside the `tExt`-checked fragment
(`tExt` rejects `throw` and `try_table`); no exception-handling coverage of the function-level or
session results is claimed by them.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.ExampleCatchExit

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- `(type (func (result i32 i32)))`. -/
def resI32x2 : RecType := ⟨[⟨true, [], .func ⟨[], [.i32, .i32]⟩⟩]⟩

/-- `(type (func (param i32 i32)))`, the tag's type. -/
def parI32x2 : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32], []⟩⟩]⟩

/-- Tag index `0`. -/
def t0 : TagIdx := ⟨0⟩

/-- Label indices `0` and `1`. -/
def l0 : LabelIdx := ⟨0, by decide⟩
def l1 : LabelIdx := ⟨1, by decide⟩

/-- The `try_table` body: `i32.const 3; i32.const 4; throw 0`. -/
def tryBody : Expr := [.intConst .i32 3, .intConst .i32 4, .throw t0]

/-- `i32.const 1; try_table (catch 0 0) (i32.const 3; i32.const 4; throw 0); unreachable`. -/
def bodyCatch : Expr := [.intConst .i32 1, .tryTable .empty [.catch_ t0 l0] tryBody, .unreachable]

/-- The block of `bodyCatchNest`: `i32.const 2; try_table (catch 0 1) (…); drop`. -/
def innerNest : Expr := [.intConst .i32 2, .tryTable .empty [.catch_ t0 l1] tryBody, .drop]

/-- `i32.const 1; block (i32.const 2; try_table (catch 0 1) (…); drop); unreachable`. -/
def bodyCatchNest : Expr := [.intConst .i32 1, .block .empty innerNest, .unreachable]

/-- The module with the tag and both bodies. -/
def catchMod : Module where
  types := [resI32x2, parI32x2]
  tags := [⟨1⟩]
  funcs := [⟨⟨0⟩, [], bodyCatch⟩, ⟨⟨0⟩, [], bodyCatchNest⟩]

/-- The executable instantiation of `catchMod` into the empty store. -/
def catchPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Nat) catchMod []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance of `catchMod`. -/
def catchStore : Store Nat := catchPrep.1.store

/-- The module instance of the functions. -/
def catchMI : ModuleInst := (catchStore.funcs[0]?.map (·.module)).getD {}

end Silmaril.Wasm.Cfg.ExampleCatchExit
