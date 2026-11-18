module

public import Silmaril.Wasm.Cfg.MachineL.Defs

/-!
# The logged machine: native against Core conventions (regression fixtures, definitions)

`bodyExtra`: `block (i32.const 1; i32.const 2); i32.const 3`, with the empty block type. It is
**not valid** (the block leaves two values with an empty result type), and it shows where the
native conventions of the logged machine `MStepL` (those of `EvalLXPS`) and the Core conventions
of `MStepC` part:

* `MStepL` leaves the block keeping its `0` result values (`EvalLXPS`'s `blockOk`:
  `vs.take nr ++ outer`), and exits with `3`;
* `MStepC` leaves it keeping the whole stack (Core's `label-vals`), and exits with `1, 2, 3`.

On valid code the two agree; no untyped correspondence between them is claimed.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.ExampleLogged

open Silmaril.Wasm

/-- The block: `i32.const 1; i32.const 2`. -/
def innerExtra : Expr := [.intConst .i32 1, .intConst .i32 2]

/-- `block (i32.const 1; i32.const 2); i32.const 3` (not valid: the block has the empty type). -/
def bodyExtra : Expr := [.block .empty innerExtra, .intConst .i32 3]

end Silmaril.Wasm.Cfg.ExampleLogged
