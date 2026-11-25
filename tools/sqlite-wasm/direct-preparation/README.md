# SQLite reactor direct preparation

`SqliteWasm.reactorDirectPreparation` proves that ordinary Core
`prepareDirect? evalConst?` succeeds for the reactor pinned by
`SqliteWasm.originalDecode`, with the canonical typed import fixture from
[the element replay](../element-init/README.md). It uses the same 23 host
addresses in order. The theorem recovers the allocation equation, applies the
ordered active element and data segments, and records their effect on the
prepared state. In particular, the function store is preserved across segment
application, function slot 25 resolves to address 25, and the Start index is
absent. The mapped memory has 131,072 bytes and contains zero words at byte
offsets 59,328 and 59,892. The read proofs use the data writes' disjointness
from those offsets.

The statement ends at executable preparation. Validated instantiation requires
a module typing judgment and linked external addresses. Calling the exported
initializer is a separate step.

Run the [whole-module check](../whole-module/README.md) first to obtain the
checked `SqliteWasm` directory, then run:

```sh
bash tools/sqlite-wasm/direct-preparation/check.sh /path/to/lean/SqliteWasm
```

The script rebuilds the focused prerequisites and compiles an ordinary
downstream import. The axiom audit is printed by Lean.
