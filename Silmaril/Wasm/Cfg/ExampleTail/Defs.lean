module

public import Silmaril.Wasm.Cfg.Machine.Defs

@[expose] public section

/-!
# Divergence through a tail callee: a regression fixture (definitions)

`tailBody x`, `block (return_call x); unreachable`: a tail call inside a block, with code after
the block that traps if it ever runs. The tail call replaces the function's frame, so the
`unreachable` is never reached. In the frame of `Abstract.recMod`'s function, where `x` names
that function, `(func (call 0))`, the tail callee recurses forever.
-/

namespace Silmaril.Wasm.Cfg.ExampleTail

open Silmaril.Wasm

/-- `return_call x`. -/
def tailInner (x : FuncIdx) : Expr := [.returnCall x]

/-- `block (return_call x); unreachable`. -/
def tailBody (x : FuncIdx) : Expr := [.block .empty (tailInner x), .unreachable]

/-- The label frame of the block. -/
def tailFrame : Machine.LFrame := ⟨0, [], false, false, [], .empty⟩

end Silmaril.Wasm.Cfg.ExampleTail
