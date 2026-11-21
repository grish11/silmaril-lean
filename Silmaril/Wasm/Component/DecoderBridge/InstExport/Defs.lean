module

public import Silmaril.Wasm.Component.InstTestsRef.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Wire.Defs

/-!
# An exported instance: the two readings name different exports (regression)

`examples/component-tests/instexport.wat` (assembled to `instexport.wasm`, 117 bytes, by the
pinned `wasm-tools` 1.262.0 as `tools/component-tests/build.sh` does) imports
`f: func(x: u32)` (unused, as in `starts` and `trap`), instantiates a core module whose `get`
returns `42`, lifts `get` at `func() -> u32`, and exports it **through an inline instance**:
`(instance $i (export "get" (func $get)))`, `(export "i" (instance $i))`.

The two readings of these bytes:

* IR (`Binary.parseComponent`, `Binary.Lower.export_`): an exported instance is flattened, each
  of its functions an IR export named `instance#function`, so the IR component
  `instExportComp` has one export, named `"i#get"`;
* REF (`Conformance.decodeRef`): the component `instExportRef` keeps the instance and its export
  `i`; the reference machine reports the **function** exports of the root instance only
  (`Reference.InstResult.instance`, `Embedding.Defs`), so after instantiating it there is no
  function export at all, and in particular none named `"i#get"`.

So `Task.startAdequacy`, as first stated (over every binary importing `f`), compares the IR's
first export by name with a reference export that does not exist. `DecoderBridge.InstExport.Thms`
states the mismatch from kernel runs. The statement `¬ Task.startAdequacy` is **not** proved: it
would need the IR play (an export answer, from the IR semantics) and that **no** reference run
reports an export `"i#get"`, while only one run is executed.

Names: `#` is not in an extern name the validators accept (`wasm-tools` rejects the export name
`i#get`: "not in kebab case"), so the flattened name cannot collide with a top-level export of
a valid component. The REF reading of the path `i`, `get` would be the instance export `i`
(`Instantiate.instantiateDef`, `.export_`), then its function `get`: the session relations
(`InstTestsRef.sessRunFrom`) look up top-level function exports by name only.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Binary (CoreMod)

/-- `examples/component-tests/instexport.wasm`. -/
def instExportBytes : ByteArray :=
  include_bytes "../../../../../examples/component-tests/instexport.wasm"

/-- The bytes of the embedded core module: `get` returns `42`. -/
def getModBytes : ByteArray := ⟨#[0, 97, 115, 109, 1, 0, 0, 0, 1, 5, 1, 96, 0, 1, 127, 3, 2, 1, 0,
  7, 7, 1, 3, 103, 101, 116, 0, 0, 10, 6, 1, 4, 0, 65, 42, 11]⟩

/-- The embedded core module as lowered: no imports, exports `get: [] → [i32]`. -/
def getCM : CoreMod := ⟨getModBytes, [], [], [("get", InstLitmus.getFt)]⟩

/-- **`instexport.wasm`, lowered**: one node, one export named `i#get`. -/
def instExportComp : Comp CoreMod :=
  .mk InstLitmus.hostI [.core getCM []]
    [⟨"i#get", ⟨[], [.u32]⟩, ⟨[.lift ⟨[], [.u32]⟩], .call 1⟩⟩]

/-- **`instexport.wasm` in the reference machine's syntax**: the export is the instance `i`. -/
def instExportRef : Core3Component :=
  InstTestsRef.fImportDefs ++
  [.coreModule (Binary.coreModule getCM), .coreInstance (.instantiate 0 []),
   .type (.func { params := [], result := some (.prim .u32) }),
   .alias (.coreExport 0 "get" .func), .canon (.lift 0 [] 1),
   .instance_ (.exports [({ name := "get" }, ⟨.func, 1⟩)]),
   .export_ { name := "i" } ⟨.instance_, 0⟩ none]

end Silmaril.Wasm.Component.DecoderBridge
