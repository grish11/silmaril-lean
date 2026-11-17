module

public import Silmaril.Wasm.Cfg.MachineL.Defs

/-!
# A validated exit from a frame holding outer values: definitions

`bodyRet`, of type `[] → [i32]`: `i32.const 1; block (result i32) (i32.const 2; return); drop`.
The `return` leaves the `block`, whose label frame holds the outer value `1`. The logged machine
`MStepL` exits with the branch-site stack `2`. `MStepC` exits with `1, 2`: it keeps the outer
values of the frames a `return` leaves (`brVals`), as Core's `return-label` unwinds them. (The
`drop` after the block only makes the body valid.)
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.ExampleRetJunk

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- `(type (func (result i32)))`. -/
def resI32 : RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩

/-- The `block` body: `i32.const 2; return`. -/
def retBlock : Expr := [.intConst .i32 2, .return_]

/-- `i32.const 1; block (result i32) (i32.const 2; return); drop`. -/
def bodyRet : Expr := [.intConst .i32 1, .block (.value .i32) retBlock, .drop]

/-- The module with `bodyRet`. -/
def retMod : Module where
  types := [resI32]
  funcs := [⟨⟨0⟩, [], bodyRet⟩]

end Silmaril.Wasm.Cfg.ExampleRetJunk
