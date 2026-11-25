# SQLite reactor data segment application

The kernel checks the original two data descriptors. Their destination
ranges in memory 0 are [1024, 52394) and [52400, 59324).
[Original decoder theorem](../whole-module/README.md) · [Artifact pin](../reactor.json)

`reactorDataApplied` gives the ordinary Core `initData? evalConst?`
equation. Its store and frame resolve memory index 0 and both data
indices, with the exact original payloads in the data entries. The
memory must contain at least 59,324 bytes. Under these premises, the
initializer applies both payloads in the original order, drops both
data entries and returns the same frame. Different payload lengths
prove that the two data entries occupy distinct store addresses.

`reactorDataMemorySize` preserves the byte length. The
`reactorDataReadAfterEnd` equation preserves every read at or above
59,324, including the initializer flag at 59,328 and the thread setup
source word at 59,892. These results use the existing closed-form
equation for the ordinary Core memory initialization loop.

After the [original decoder check](../whole-module/README.md#reproduce), run

```sh
bash tools/sqlite-wasm/data-application/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

The downstream check imports `SqliteWasm.DataApplication`, connects
the application equation to `originalDecode`, checks both startup reads
and audits the public theorem axioms.
[Statements](DataApplication.lean) · [Downstream check](ImportCheck.lean)
