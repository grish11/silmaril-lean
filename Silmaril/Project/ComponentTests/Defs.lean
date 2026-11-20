module

public import Silmaril.Project.Shapes.ComponentTest.Defs
public import Silmaril.Wasm.Component.InstTests.Defs

/-! # Component test rows

Rows of the component test shapes (`silmaril.shapes.component.test.*`) on the two binaries of
`examples/component-tests` (`Silmaril.Wasm.Component.InstTests`), assembled with the pinned
`wasm-tools` 1.262.0 (`tools/component-tests/build.sh`):

| row | shape | binary | statement |
|---|---|---|---|
| `silmaril.component_tests.starts.instantiates` | `instantiates` | `starts.wasm` | instantiation calls `f(u32 1)`, then `f(u32 2)` (answered `()` by the typed host `unitHost`), then is `ready`; at deterministic profiles nothing else |
| `silmaril.component_tests.starts.get_after_inst` | `export_returns_after_inst` | `starts.wasm` | after that instantiation, `get()` returns `u32 42` (the value the third instance's start function wrote); at deterministic profiles only `42` |
| `silmaril.component_tests.trap.inst_traps` | `inst_traps` | `trap.wasm` | the first start function traps: the whole instantiation fails (`fail ()`) with no import call; at deterministic profiles never `ready`, no import call, no export answered |

Answered in `Silmaril.Project.ComponentTests.Thms`. The pinned wasmtime 50.0.0 agrees on both
binaries (`examples/component-tests/oracle.json`, not a proof).
-/

silmaril instance silmaril.component_tests.starts.instantiates (expect := "THM")
    (title := "starts.wasm: instantiation calls f(1), then f(2), then is ready") :=
  silmaril.shapes.component.test.instantiates (b := Silmaril.Wasm.Component.InstTests.startsBytes)
  (host := Silmaril.Wasm.Component.InstTests.unitHost)
  (tr := Silmaril.Wasm.Component.InstTests.startsTrace)

silmaril instance silmaril.component_tests.starts.get_after_inst (expect := "THM")
    (title := "starts.wasm: after instantiation, get() returns 42 (written by a start function)") :=
  silmaril.shapes.component.test.export_returns_after_inst
  (b := Silmaril.Wasm.Component.InstTests.startsBytes)
  (host := Silmaril.Wasm.Component.InstTests.unitHost)
  (tr := Silmaril.Wasm.Component.InstTests.startsTrace)
  (q := Silmaril.Wasm.Component.InstTests.getV) (v := Silmaril.Wasm.Component.InstTests.v42)

silmaril instance silmaril.component_tests.trap.inst_traps (expect := "THM")
    (title := "trap.wasm: a trapping start function fails the whole instantiation") :=
  silmaril.shapes.component.test.inst_traps (b := Silmaril.Wasm.Component.InstTests.trapBytes)
  (host := Silmaril.Wasm.Component.InstTests.unitHost) (tr := [])
