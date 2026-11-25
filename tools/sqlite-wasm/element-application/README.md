# SQLite reactor element segment application

The original decoded reactor has one active element segment with
342 references, table index 0 and i32 offset 1. It declares one i32
table with a minimum length of 343.
[Original decoder theorem](../whole-module/README.md) · [Artifact pin](../reactor.json)

`reactorElementPhase` proves an equation for the ordinary Core
`initElem? evalConst?`. The supplied frame and store must resolve
table 0 and element segment 0. The table must have at least 343 entries,
and the segment must hold its 342 references. The result installs those
references at indices 1 through 342, preserves the surrounding entries,
drops the segment entries and returns the original frame.

The proof uses the existing structural equation for the ordinary Core
table-initialization loop. Its premises describe the allocated table
and segment. Evaluation of the reference expressions and construction of
the allocated store precede this phase.

After the [original decoder check](../whole-module/README.md#reproduce), run

```sh
bash tools/sqlite-wasm/element-application/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

The downstream module imports `SqliteWasm.ElementApplication` from the
generated Lean root, exercises the ordinary equation through
`originalDecode`, and audits its axiom dependencies.
[Statements](ElementApplication.lean) · [Downstream check](ImportCheck.lean)
