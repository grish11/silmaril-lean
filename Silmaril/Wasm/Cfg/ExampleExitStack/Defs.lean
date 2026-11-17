module

public import Silmaril.Wasm.Cfg.Machine.Defs

@[expose] public section

/-!
# Leaving the function from inside a block: regression fixtures (definitions)

A function's exit carries the **whole frame stack**: the values a block's label frames keep
outside the block (`LFrame.outer`), under the block's own (`Machine.brVals`), as Core's
`return-label` and branch-through-label rules unwind them. These bodies, of type
`[] → [i32 i32]`, push `1` outside a block and leave the function from inside it:

* `bodyRet`: `i32.const 1; block (i32.const 2; i32.const 3; return); i32.const 4`;
* `bodyBr`: `i32.const 1; block (i32.const 2; i32.const 3; br 1); i32.const 4`;
* `bodyBrIf k`: `i32.const 1; block (i32.const 2; i32.const 3; i32.const k; br_if 1; drop; drop);
  drop; i32.const 4; i32.const 5` (taken for `k ≠ 0`, not taken for `0`);
* `bodyTable`: `i32.const 1; block (i32.const 2; i32.const 3; i32.const 0; br_table [1] 1);
  i32.const 4`.

(The final `i32.const 4` after a block that never falls through only makes the body valid.)

Core returns the top two values (`2, 3`, or `4, 5` when `br_if` is not taken); the machine's
exit stack is the whole stack `1, 2, 3`. `exitMod` validates.

`bodyLoss`: `i32.const 1; block (i32.const 2; return)`, of type `[] → [i32 i32]`, is not valid
(the block's `return` has one value), but Core returns `1, 2`: the returned values reach below
the block. The machine keeps `1` and exits with `1, 2`; before the exit kept the whole stack it
exited with `2` alone. This fixture is about the exit state only: untyped tail calls are not
covered (`Region.TailWF`).
-/

namespace Silmaril.Wasm.Cfg.ExampleExitStack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- `(type (func (result i32 i32)))`. -/
def resI32x2 : RecType := ⟨[⟨true, [], .func ⟨[], [.i32, .i32]⟩⟩]⟩

/-- Label index `1`. -/
def l1 : LabelIdx := ⟨1, by decide⟩

/-- The block of `bodyRet`. -/
def innerRet : Expr := [.intConst .i32 2, .intConst .i32 3, .return_]
/-- `i32.const 1; block (i32.const 2; i32.const 3; return); i32.const 4`. -/
def bodyRet : Expr := [.intConst .i32 1, .block .empty innerRet, .intConst .i32 4]

/-- The block of `bodyBr`. -/
def innerBr : Expr := [.intConst .i32 2, .intConst .i32 3, .br l1]
/-- `i32.const 1; block (i32.const 2; i32.const 3; br 1); i32.const 4`. -/
def bodyBr : Expr := [.intConst .i32 1, .block .empty innerBr, .intConst .i32 4]

/-- The block of `bodyBrIf k`. -/
def innerBrIf (k : BitVec 32) : Expr :=
  [.intConst .i32 2, .intConst .i32 3, .intConst .i32 k, .brIf l1, .drop, .drop]
/-- `i32.const 1; block (…; i32.const k; br_if 1; drop; drop); drop; i32.const 4; i32.const 5`. -/
def bodyBrIf (k : BitVec 32) : Expr :=
  [.intConst .i32 1, .block .empty (innerBrIf k), .drop, .intConst .i32 4, .intConst .i32 5]

/-- The block of `bodyTable`. -/
def innerTable : Expr := [.intConst .i32 2, .intConst .i32 3, .intConst .i32 0, .brTable [l1] l1]
/-- `i32.const 1; block (i32.const 2; i32.const 3; i32.const 0; br_table [1] 1); i32.const 4`. -/
def bodyTable : Expr := [.intConst .i32 1, .block .empty innerTable, .intConst .i32 4]

/-- The module with the typed bodies. -/
def exitMod : Module where
  types := [resI32x2]
  funcs := [⟨⟨0⟩, [], bodyRet⟩, ⟨⟨0⟩, [], bodyBr⟩, ⟨⟨0⟩, [], bodyBrIf 1⟩, ⟨⟨0⟩, [], bodyBrIf 0⟩,
    ⟨⟨0⟩, [], bodyTable⟩]

/-- The block of `bodyLoss`. -/
def innerLoss : Expr := [.intConst .i32 2, .return_]
/-- `i32.const 1; block (i32.const 2; return)` (not valid at `[] → [i32 i32]`). -/
def bodyLoss : Expr := [.intConst .i32 1, .block .empty innerLoss]

/-- The label frame of the block: arity `0`, the outer value `1`. -/
def frameOne : Machine.LFrame := ⟨0, [.i32 1], false, false, [], .empty⟩

end Silmaril.Wasm.Cfg.ExampleExitStack
