module

public import Silmaril.Wasm.Component.InstLitmus.Defs
public import Silmaril.Wasm.Component.Binary.Lower.SemI.Defs
public import Silmaril.Data.IncludeBytes

/-!
# Component test binaries: instantiation-time behaviour

Two component binaries, assembled from `examples/component-tests/{starts,trap}.wat` by the
pinned `wasm-tools` 1.262.0 (`parse`, then `strip --all`, then `validate`;
`tools/component-tests/build.sh` reproduces them byte for byte), read here with `include_bytes`.

**`starts.wasm`** (256 bytes) imports one host function `f: func(x: u32)` and has three core
instances, instantiated in order:

* `call1`: imports `env.f: [i32] → []`; its start function is `i32.const 1; call 0`;
* `call2`: the same with `i32.const 2`;
* `glob`: a mutable global initialised to `0`; its start function stores `42` into it; it exports
  `get: [] → [i32]`, which returns the global.

`f` is wired to both `call` instances through `canon lower`; the component exports
`get: func() -> u32`, `glob`'s `get` through `canon lift`. Instantiating it calls `f(1)` and then
`f(2)`, and afterwards `get()` returns `42` (it would return `0` if `glob`'s start function had
not run).

**`trap.wasm`** (188 bytes) imports the same `f` and has two core instances: `trap`, whose start
function is `unreachable` and which exports `get` (returning `7`), then `call2` as above. It
exports `trap`'s `get`. Its instantiation traps in the first start function: `f(2)` is never
called and `get` is never available.

Definitions:

* `startsBytes`, `trapBytes`: the bytes;
* `startsComp`, `trapComp : Comp Binary.CoreMod`: the components `Binary.parseComponent` lowers
  them to (`InstTests.Thms`: `parse_starts`, `parse_trap`, by the kernel's definitional check); the
  embedded core modules are `call1CM`, `call2CM`, `globCM`, `trapCM`, whose bytes the core decoder
  reads as the litmus modules `callCore3 1`, `callCore3 2`, `globCore3`, `trapCore3`
  (`Silmaril.Wasm.Component.InstLitmus`);
* `startsC`, `trapLC : Comp ImpModule`: the same components over the litmus modules, read by
  `Param.core3SemI`;
* the moves at the component's interface (`sigU`, component values): `fV k` is the host call
  `f(u32 k)`, `unitV` its answer `()`, `getV` the export call `get()`, `v42` the answer `u32 42`;
  `unitHost` is the typed host of `f` (it answers every call `()`); `startsTrace` is the expected
  ordered import trace `[f(1) ↦ (), f(2) ↦ ()]`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.InstTests

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.Binary (CoreMod)

/-! ## The binaries -/

/-- `examples/component-tests/starts.wasm`. -/
def startsBytes : ByteArray := include_bytes "../../../../examples/component-tests/starts.wasm"

/-- `examples/component-tests/trap.wasm`. -/
def trapBytes : ByteArray := include_bytes "../../../../examples/component-tests/trap.wasm"

/-! ## The embedded core modules -/

/-- The bytes of `call1` (`callCore3 1`). -/
def call1Bytes : ByteArray := ⟨#[0, 97, 115, 109, 1, 0, 0, 0, 1, 8, 2, 96, 1, 127, 0, 96, 0, 0, 2,
  9, 1, 3, 101, 110, 118, 1, 102, 0, 0, 3, 2, 1, 1, 8, 1, 1, 10, 8, 1, 6, 0, 65, 1, 16, 0, 11]⟩

/-- The bytes of `call2` (`callCore3 2`). -/
def call2Bytes : ByteArray := ⟨#[0, 97, 115, 109, 1, 0, 0, 0, 1, 8, 2, 96, 1, 127, 0, 96, 0, 0, 2,
  9, 1, 3, 101, 110, 118, 1, 102, 0, 0, 3, 2, 1, 1, 8, 1, 1, 10, 8, 1, 6, 0, 65, 2, 16, 0, 11]⟩

/-- The bytes of `glob` (`globCore3`). -/
def globBytes : ByteArray := ⟨#[0, 97, 115, 109, 1, 0, 0, 0, 1, 8, 2, 96, 0, 0, 96, 0, 1, 127, 3,
  3, 2, 0, 1, 6, 6, 1, 127, 1, 65, 0, 11, 7, 7, 1, 3, 103, 101, 116, 0, 1, 8, 1, 0, 10, 13, 2, 6,
  0, 65, 42, 36, 0, 11, 4, 0, 35, 0, 11]⟩

/-- The bytes of `trap` (`trapCore3`). -/
def trapModBytes : ByteArray := ⟨#[0, 97, 115, 109, 1, 0, 0, 0, 1, 8, 2, 96, 0, 0, 96, 0, 1, 127,
  3, 3, 2, 0, 1, 7, 7, 1, 3, 103, 101, 116, 0, 1, 8, 1, 0, 10, 10, 2, 3, 0, 0, 11, 4, 0, 65, 7,
  11]⟩

/-- `call1` as lowered: imports `env.f: [i32] → []`, no exports. -/
def call1CM : CoreMod := ⟨call1Bytes, [("env", "f")], [("f", fFt)], []⟩

/-- `call2` as lowered. -/
def call2CM : CoreMod := ⟨call2Bytes, [("env", "f")], [("f", fFt)], []⟩

/-- `glob` as lowered: no imports, exports `get: [] → [i32]`. -/
def globCM : CoreMod := ⟨globBytes, [], [], [("get", getFt)]⟩

/-- `trap` as lowered: no imports, exports `get: [] → [i32]`. -/
def trapCM : CoreMod := ⟨trapModBytes, [], [], [("get", getFt)]⟩

/-! ## The components -/

/-- The wiring of `f` into a core instance: `canon lower` of import `0`. -/
def lowF : List Impl := [⟨[.lower ⟨[.u32], []⟩], .call 0⟩]

/-- The export `get: func() -> u32`: `canon lift` of environment function `r`. -/
def getL (r : Nat) : Export := ⟨"get", ⟨[], [.u32]⟩, ⟨[.lift ⟨[], [.u32]⟩], .call r⟩⟩

/-- **`starts.wasm`, lowered.** -/
def startsComp : Comp CoreMod :=
  .mk hostI [.core call1CM lowF, .core call2CM lowF, .core globCM []] [getL 1]

/-- **`trap.wasm`, lowered.** -/
def trapComp : Comp CoreMod := .mk hostI [.core trapCM [], .core call2CM lowF] [getL 1]

/-- `starts.wasm` over the litmus modules. -/
def startsC : Comp ImpModule :=
  .mk hostI [.core (callMod 1) lowF, .core (callMod 2) lowF, .core globMod []] [getL 1]

/-- `trap.wasm` over the litmus modules. -/
def trapLC : Comp ImpModule := .mk hostI [.core trapMod [], .core (callMod 2) lowF] [getL 1]

/-! ## Moves -/

/-- The host call `f(u32 k)`. -/
def fV (k : BitVec 32) : sigU.Op := (0, .vals [.u32 k])

/-- The answer `()` to a call of `f`. -/
def unitV : Option Payload := some (.vals [])

/-- The export call `get()`. -/
def getV : sigU.Op := (0, .vals [])

/-- The answer `u32 42`. -/
def v42 : Option Payload := some (.vals [.u32 42])

/-- **The typed host of `f: func(x: u32)`**: every call is answered `()`. -/
def unitHost : sigU.Op → Option Payload := fun _ => unitV

/-- **The expected import trace of `starts.wasm`**: `f(1)`, then `f(2)`, each answered `()`. -/
def startsTrace : List (Σ _ : sigU.Op, Option Payload) := [⟨fV 1, unitV⟩, ⟨fV 2, unitV⟩]

end Silmaril.Wasm.Component.InstTests
