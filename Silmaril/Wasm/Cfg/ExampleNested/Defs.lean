module

public import Silmaril.Wasm.Cfg.MachineL.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.ConstEval

/-!
# Validated typed nested fixtures for the block-CFG machines (definitions)

Three valid function bodies nesting structured control, on which the logged machine `MStepL`
(native conventions) and the Core-convention machine `MStepC` reach the same exit state
(`Silmaril.Wasm.Cfg.ExampleNested.Thms`). `nestMod` declares them, with the tag
`0 : [i32] → []`, and validates.

* `bodyNest` (`[] → [i32 i32]`): `i32.const 9; block (result i32) (loop (i32.const 1;
  if (i32.const 42; br 2))); i32.const 0)`. The `br 2` leaves the `if` and the `loop` for the
  `block`, which keeps `42` over the outer `9`. It returns `9, 42`.
* `bodyLoops` (`[] → [i32]`, one `i32` local, the counter): `loop (loop (local.get 0; i32.eqz;
  local.get 0; i32.const 1; i32.add; local.set 0; br_if 1)); local.get 0`. The inner loop's
  `br_if 1` targets the **outer** loop's label: on the first pass (counter `0`) it is taken and
  re-enters the outer loop, on the second (counter `1`) it falls through both loops. It returns
  the counter, `2`.
* `bodyTry` (`[] → [i32]`): `i32.const 1; block (result i32) (try_table (catch 0 0)
  (block (i32.const 3; throw 0)); unreachable); i32.add`. The exception thrown inside the
  nested block is caught by the `try_table`'s clause, a branch to the outer `block` with the
  payload `3` over the outer `1`; `i32.add` then returns `4`.

(The `i32.const 0` and the `unreachable` after constructs that never fall through only make the
bodies valid.) `nestStore` is the store the executable instantiation `nestPrep` allocates and
`nestMI` the functions' module instance: there the tag hypotheses of `bodyTry` hold.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.ExampleNested

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- `(type (func (result i32 i32)))`. -/
def resI32x2 : RecType := ⟨[⟨true, [], .func ⟨[], [.i32, .i32]⟩⟩]⟩

/-- `(type (func (result i32)))`. -/
def resI32 : RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩

/-- `(type (func (param i32)))`, the tag's type. -/
def parI32 : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩

/-- Label indices `0`, `1` and `2`. -/
def l0 : LabelIdx := ⟨0, by decide⟩
def l1 : LabelIdx := ⟨1, by decide⟩
def l2 : LabelIdx := ⟨2, by decide⟩

/-- Local index `0`. -/
def x0 : LocalIdx := ⟨0, by decide⟩

/-- Tag index `0`. -/
def t0 : TagIdx := ⟨0⟩

/-! ## `bodyNest`: `block`, `loop`, `if` and a branch across two labels -/

/-- The `if` arm: `i32.const 42; br 2`. -/
def nestThen : Expr := [.intConst .i32 42, .br l2]

/-- The `loop` body: `i32.const 1; if (…)`. -/
def nestLoop : Expr := [.intConst .i32 1, .if_ .empty nestThen []]

/-- The `block` body: `loop (…); i32.const 0`. -/
def nestBlock : Expr := [.loop .empty nestLoop, .intConst .i32 0]

/-- `i32.const 9; block (result i32) (loop (i32.const 1; if (i32.const 42; br 2)));
i32.const 0)`. -/
def bodyNest : Expr := [.intConst .i32 9, .block (.value .i32) nestBlock]

/-! ## `bodyLoops`: an inner loop continuing the outer loop -/

/-- The inner loop's body: `local.get 0; i32.eqz; local.get 0; i32.const 1; i32.add;
local.set 0; br_if 1` (branch to the outer loop when the old counter is `0`). -/
def loopsInner : Expr :=
  [.localGet x0, .intTestOp .i32 .eqz, .localGet x0, .intConst .i32 1, .intBinOp .i32 .add,
    .localSet x0, .brIf l1]

/-- The outer loop's body: the inner loop. -/
def loopsOuter : Expr := [.loop .empty loopsInner]

/-- `loop (loop (…; br_if 1)); local.get 0`. -/
def bodyLoops : Expr := [.loop .empty loopsOuter, .localGet x0]

/-- The function's frame with the counter `k` in its local `0`. -/
def frameK (k : BitVec 32) (mi : ModuleInst) : Frame := ⟨[some (.i32 k)], mi⟩

/-- A `loop`'s label frame with the empty block type and no outer values. -/
abbrev loopFrame : Machine.LFrame := ⟨0, [], true, false, [], .empty⟩

/-- The machine at the inner loop's body (the block of its `br_if 1`), inside both loops, on
the counter `k`. -/
def innerAt {H : Type} (s : Store H) (k : BitVec 32) (mi : ModuleInst) : Machine.MState H :=
  ⟨.block ⟨[(0, 0), (0, 0)], 0⟩, [], [loopFrame, loopFrame], s, frameK k mi⟩

/-- The machine at the outer loop's body (the block opening the inner loop), inside the outer
loop only, on the counter `k`. -/
def outerAt {H : Type} (s : Store H) (k : BitVec 32) (mi : ModuleInst) : Machine.MState H :=
  ⟨.block ⟨[(0, 0)], 0⟩, [], [loopFrame], s, frameK k mi⟩

/-! ## `bodyTry`: a caught `throw` inside a nested block -/

/-- The nested block: `i32.const 3; throw 0`. -/
def tryInner : Expr := [.intConst .i32 3, .throw t0]

/-- The `try_table` body: `block (i32.const 3; throw 0)`. -/
def tryBody : Expr := [.block .empty tryInner]

/-- The outer block's body: `try_table (catch 0 0) (…); unreachable`. -/
def tryBlock : Expr := [.tryTable .empty [.catch_ t0 l0] tryBody, .unreachable]

/-- `i32.const 1; block (result i32) (try_table (catch 0 0) (block (i32.const 3; throw 0));
unreachable); i32.add`. -/
def bodyTry : Expr := [.intConst .i32 1, .block (.value .i32) tryBlock, .intBinOp .i32 .add]

/-- The module with the tag and the three bodies. -/
def nestMod : Module where
  types := [resI32x2, resI32, parI32]
  tags := [⟨2⟩]
  funcs := [⟨⟨0⟩, [], bodyNest⟩, ⟨⟨1⟩, [.i32], bodyLoops⟩, ⟨⟨1⟩, [], bodyTry⟩]

/-- The executable instantiation of `nestMod` into the empty store. -/
def nestPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Nat) nestMod []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance of `nestMod`. -/
def nestStore : Store Nat := nestPrep.1.store

/-- The module instance of the functions. -/
def nestMI : ModuleInst := (nestStore.funcs[0]?.map (·.module)).getD {}

end Silmaril.Wasm.Cfg.ExampleNested
