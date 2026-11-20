module

public import Silmaril.Wasm.Component.InstTestsRef.Defs

/-!
# A parameter name the host does not have (counterexample)

`examples/component-tests/paramname.wat` (assembled to `paramname.wasm`, 256 bytes, by the
pinned `wasm-tools` 1.262.0 as `tools/component-tests/build.sh` does) is `starts.wat` with the
import declared as `f: func(y: u32)` instead of `f: func(x: u32)`; the binary differs from
`starts.wasm` in that one byte.

* IR (`Binary.parseComponent`): parameter names are dropped, so the IR reading is
  `InstTests.startsComp`, imports `hostI` included, and its plays are those of `starts.wasm`;
* REF (`Conformance.decodeRef`): `paramNameRef`, `startsRef` with the parameter renamed. It is
  valid and in the fragment `InFrag`. The reference machine links the root import against the
  host function `f: func(x: u32)` of `hostConfigX` **by name**, so the pre-check of the root
  instantiation fails and the instantiation traps before any side effect.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference

/-- `examples/component-tests/paramname.wasm`. -/
def paramNameBytes : ByteArray :=
  include_bytes "../../../../../examples/component-tests/paramname.wasm"

/-- **`paramname.wasm` in the reference machine's syntax**: `startsRef` with the parameter of the
imported function type named `y`. -/
def paramNameRef : Core3Component :=
  [.type (.func { params := [("y", .prim .u32)], result := none }),
   .import_ { name := "f" } (.func 0)] ++ InstTestsRef.startsRef.drop 2

end Silmaril.Wasm.Component.DecoderBridge
