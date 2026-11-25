# Linked SQLite reactor initializer

The pinned reactor has no Start section and exports slot 25 as
`_initialize`. The declarations also specify exclusively function imports,
a zero initializer for defined global 1, and one two-page i32 memory.
These are facts from the same decoded bytes.
[Intrinsic constructor and export](../intrinsic-initializer/README.md) · [Original decode](../whole-module/README.md)

`initializerReturns` composes the Core reductions for the original flag
write and calls to slots 1516 and 23. A zero flag, resolved Wasm function
entries with empty parameter and result types, and already linked memory
and global mappings suffice. The initializer and setup call select the same
memory, which contains at least 59,984 bytes. The result returns no values
with the caller frame restored and one memory instance updated by the
mark and eight ordered setup writes. The same proof covers Core `invoke`
at the resolved function address and its empty outer frame.
[Flag paths](../initializer-flag/README.md) · [Setup effects](../wasi-thread-setup/README.md)

`initializerTrapsOnNonzero` gives the trap reduction from a linked call
to slot 25 under a successful nonzero flag load. It leaves the store and
caller frame intact and needs no linkage premises for the unexecuted
callees. The address-based `invoke` form reaches the same trap.
`initializerFlagStaysMarked` shows that the eight setup writes
preserve the mark at the pinned zero base.

`initializerReturnsAfterAllocation` derives the three function entries and
their signatures from successful Core allocation with 23 function addresses.
It resolves the allocated export address, proves `InvokeOk` for the empty
argument list, and shows the `invoke` reduction at that address. The
conditional theorem applies to a runtime store that retains the allocated function entries and
provides the stated memory, global and flag. Both execution paths use Core
reductions without host calls.
[Allocation bindings](../startup-bindings/README.md)

After building the [original decoder theorem](../whole-module/README.md#reproduce), run

```sh
bash tools/sqlite-wasm/linked-initializer/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

This builds the four prerequisite proof modules and tests the ordinary
import `SqliteWasm.InitializerStartup`, including the axiom audit.
[Statements](InitializerStartup.lean) · [Downstream check](ImportCheck.lean)
