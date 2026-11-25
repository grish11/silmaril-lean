# SQLite reactor Core preparation

`reactorPrepared` proves that ordinary `prepare? evalConst?` succeeds
for the pinned reactor with the 23 typed import entries at the canonical
addresses from the element-expression replay. Its returned configuration
has function slot 25 at store address 25. The accompanying Start index
is absent. [Original decode](../whole-module/README.md) · [Import fixture and reference evaluation](../element-init/README.md)

The checked segment guard covers both data payloads and the 342-entry
element vector. The proof composes the ordinary initializer equations
with successful type and export lookups, so the kernel can project
the function address without reducing the full allocated store.
The result covers preparation, which produces the configuration for
segment application. The import fixture gives typed function entries
for that computation.

After the [original decoder check](../whole-module/README.md#reproduce), run

```sh
bash tools/sqlite-wasm/core-preparation/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

This checks the element prerequisite before compiling the guard,
preparation proof and ordinary downstream import. The downstream
import connects the preparation theorem to the pinned decoder equation
and audits its axioms. [Statements](CorePreparation.lean) · [Downstream check](ImportCheck.lean)
