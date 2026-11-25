# SQLite reactor startup bindings

`allocatedStartupBindings` uses inversion of ordinary Core
`allocModule?`. When allocation succeeds for the pinned reactor and the
supplied addresses contain 23 function addresses, slots 23, 25 and 1516
resolve to their original Wasm definitions. Each resolved entry uses the
allocated module instance. Its allocated type expands to `() → ()`.
The kernel checks the selected defined ordinals 0, 2 and 1493 and their
runtime type expansions from the quoted module.
[Original decoder theorem](../whole-module/README.md) · [Artifact pin](../reactor.json)

`allocatedInitializeExport` checks that the allocated `_initialize`
export names the same store address as slot 25. The ordinary downstream
import uses both this theorem and the original decoder equation.

Both results concern successful allocation and the resulting store and
module instance. Initialization of segments and execution of the exported
initializer are subsequent stages with their own premises.

After the [original decoder check](../whole-module/README.md#reproduce), run

```sh
bash tools/sqlite-wasm/startup-bindings/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

Import `SqliteWasm.StartupBindings` from the generated Lean root. The
downstream check prints both public theorems' axiom dependencies.
[Statements](StartupBindings.lean) · [Downstream check](ImportCheck.lean)
