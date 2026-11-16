module

public import Silmaril.Wasm.Cfg.Machine.Defs

@[expose] public section

/-!
# Calls by reference in the block-CFG machine: regression fixtures (definitions)

Two one-block bodies that end in `call_ref y`:

* `refBody x y`: `ref.func x; call_ref y`, a call by reference of function `x`. In the frame of
  `Abstract.recMod`'s function, where `x` names that function, `(func (call 0))`, the callee
  recurses forever, so the call diverges inside the callee.
* `nullBody ht y`: `ref.null ht; call_ref y`, a call by reference of null, which traps
  (`call_ref-null`) and never diverges.
-/

namespace Silmaril.Wasm.Cfg.ExampleRef

open Silmaril.Wasm

/-- `ref.func x; call_ref y`. -/
def refBody (x : FuncIdx) (y : TypeIdx) : List Instr := [.refFunc x, .callRef y]

/-- `ref.null ht; call_ref y`. -/
def nullBody (ht : HeapType) (y : TypeIdx) : List Instr := [.refNull ht, .callRef y]

end Silmaril.Wasm.Cfg.ExampleRef
