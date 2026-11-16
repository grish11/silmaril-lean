module

public import Silmaril.Wasm.Component.Param.Start.Defs
public import Silmaril.Wasm.Component.Reference.Start.Defs
public import Silmaril.Wasm.Component.Binary.Lower.Defs

/-!
# Start functions on the Core 3.0 engine: litmus modules

Regression modules for `Param.engineSemS` over `Reference.core3P P`, read as `NumModule`s
through `NumModule.mod`:

* `Reference.Litmus.startMod` (from `Reference.Start`): the start function stores `42` in a
  mutable global, and the export `get` reads it;
* `trapStartMod`: the start function is `unreachable`, and the export `get` returns `7`.

The same two modules as hand-assembled binaries, lowered core modules for
`Binary.coreModSemLazyStart` (`startCM`, `trapCM`): the theorems about them are about what their bytes
decode to (`Binary.coreModule`), computed in the kernel.

`getQ` is the question `get()` of these modules. The theorems are in `StartCore3.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Param.StartCore3

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference

/-- A module whose start function traps:
`(func $start unreachable) (func (export "get") (result i32) i32.const 7) (start $start)`. -/
def trapStartCore3 : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.unreachable]⟩, ⟨⟨1⟩, [], [.intConst .i32 7]⟩]
  exports := [⟨"get", .func ⟨1⟩⟩]
  start := some ⟨0⟩

/-- The module with its export interface. -/
def trapStartMod : NumModule := ⟨trapStartCore3, [("get", ⟨[], [.int .i32]⟩)]⟩

/-- A binary of the module of `Reference.Litmus.startCore3`: types `[] → []` and `[] → [i32]`, a
mutable `i32` global initialised to `0`, the start function `i32.const 42; global.set 0`, and
the export `get` running `global.get 0`. -/
def startBytes : ByteArray := ⟨#[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x08, 0x02, 0x60, 0x00, 0x00, 0x60, 0x00, 0x01, 0x7f,
  0x03, 0x03, 0x02, 0x00, 0x01,
  0x06, 0x06, 0x01, 0x7f, 0x01, 0x41, 0x00, 0x0b,
  0x07, 0x07, 0x01, 0x03, 0x67, 0x65, 0x74, 0x00, 0x01,
  0x08, 0x01, 0x00,
  0x0a, 0x0d, 0x02, 0x06, 0x00, 0x41, 0x2a, 0x24, 0x00, 0x0b, 0x04, 0x00, 0x23, 0x00, 0x0b]⟩

/-- `startBytes` as a lowered core module exporting `get: [] → [i32]`. -/
def startCM : Silmaril.Wasm.Component.Binary.CoreMod :=
  ⟨startBytes, [], [], [("get", ⟨[], [.int .i32]⟩)]⟩

/-- A binary of the module of `trapStartCore3`: the start function `unreachable`, the export
`get` returning `i32.const 7`. -/
def trapBytes : ByteArray := ⟨#[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x08, 0x02, 0x60, 0x00, 0x00, 0x60, 0x00, 0x01, 0x7f,
  0x03, 0x03, 0x02, 0x00, 0x01,
  0x07, 0x07, 0x01, 0x03, 0x67, 0x65, 0x74, 0x00, 0x01,
  0x08, 0x01, 0x00,
  0x0a, 0x0a, 0x02, 0x03, 0x00, 0x00, 0x0b, 0x04, 0x00, 0x41, 0x07, 0x0b]⟩

/-- `trapBytes` as a lowered core module exporting `get: [] → [i32]`. -/
def trapCM : Silmaril.Wasm.Component.Binary.CoreMod :=
  ⟨trapBytes, [], [], [("get", ⟨[], [.int .i32]⟩)]⟩

/-- The question `get()`. -/
def getQ : (sigN 1).Op := (0, .flat [])

end Silmaril.Wasm.Component.Param.StartCore3
