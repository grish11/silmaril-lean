module

public import Silmaril.Wasm.Cfg.Machine.Defs

@[expose] public section

/-!
# Branches to the function label: regression fixtures (definitions)

A function body runs under its function's label (Core `FRAME_n{} (LABEL_n{} body)`), so a branch
whose depth is the body's nesting depth targets the function boundary and returns. The native
store check accepts it (`Interp.StoreChkE` checks bodies under the labels `[rs.length]`), and the
extracted CFG resolves the outermost label to the `exit` sink (`labels body [] = [.exit]`).

`brOutMod` is a validated module with five such functions:

* `body0`: `i32.const 1; br 0` (type `[] → [i32]`): returns `1`;
* `body1`: `i32.const 7; i32.const 1; br_if 0; drop; i32.const 9`: the branch is taken, returns `7`;
* `body2`: the same with condition `0`: the branch is not taken, returns `9`;
* `body3`: `block (i32.const 5; i32.const 0; br_table [1] 1); i32.const 0`: a `br_table` from
  inside a block to the function label (depth `1`), returns `5`;
* `body4`: `i32.const 1; i32.const 2; br 0` (type `[] → [i32, i32]`): returns `1, 2`.
-/

namespace Silmaril.Wasm.Cfg.ExampleBrOut

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- `(type (func (result i32)))`. -/
def resI32 : RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩

/-- `(type (func (result i32 i32)))`. -/
def resI32x2 : RecType := ⟨[⟨true, [], .func ⟨[], [.i32, .i32]⟩⟩]⟩

/-- Label index `0`. -/
def l0 : LabelIdx := ⟨0, by decide⟩

/-- Label index `1`. -/
def l1 : LabelIdx := ⟨1, by decide⟩

/-- `i32.const 1; br 0`. -/
def body0 : Expr := [.intConst .i32 1, .br l0]

/-- `i32.const 7; i32.const 1; br_if 0; drop; i32.const 9`. -/
def body1 : Expr := [.intConst .i32 7, .intConst .i32 1, .brIf l0, .drop, .intConst .i32 9]

/-- `i32.const 7; i32.const 0; br_if 0; drop; i32.const 9`. -/
def body2 : Expr := [.intConst .i32 7, .intConst .i32 0, .brIf l0, .drop, .intConst .i32 9]

/-- The block inside `body3`: `i32.const 5; i32.const 0; br_table [1] 1`. -/
def inner3 : Expr := [.intConst .i32 5, .intConst .i32 0, .brTable [l1] l1]

/-- `block (i32.const 5; i32.const 0; br_table [1] 1); i32.const 0`. -/
def body3 : Expr := [.block .empty inner3, .intConst .i32 0]

/-- `i32.const 1; i32.const 2; br 0`. -/
def body4 : Expr := [.intConst .i32 1, .intConst .i32 2, .br l0]

/-- The module with the five functions. -/
def brOutMod : Module where
  types := [resI32, resI32x2]
  funcs := [⟨⟨0⟩, [], body0⟩, ⟨⟨0⟩, [], body1⟩, ⟨⟨0⟩, [], body2⟩, ⟨⟨0⟩, [], body3⟩,
    ⟨⟨1⟩, [], body4⟩]

/-- The machine's label frame of `body3`'s block (arity `0`, no outer values). -/
def frame3 : Machine.LFrame := ⟨0, [], false, false, [], .empty⟩

end Silmaril.Wasm.Cfg.ExampleBrOut
