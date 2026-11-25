# Recovering completed SQLite VFS exchanges

The container machine emits a receive event when it accepts a request
and a send event when the handler returns a typed exchange.
`completed` selects the sends from an event list. `completed_encode`
proves that this projection recovers a trace from its encoding.
[Definition](../../Silmaril/Containers/SqliteVfs/Completed/Defs.lean) ·
[Container machine](../../Silmaril/Containers/SqliteVfs/Defs.lean)

`completed_exec_iff` characterizes finite executions from the idle
state. The projection is a valid backing trace to a current state.
The event list and the ending phase have one of two shapes.

- The list encodes precisely the completed exchanges, and the current
  state is idle.
- The same encoding is followed by one receive, and the current state
  is pending with that request. The request contributes no exchange.

`completed_blocked_iff` characterizes the blocked runtime observation
by exact encoding and backing trace validity. Its event list consists
of completed pairs. This also rejects a send with no corresponding
receive, even when filtering the sends produces a valid backing trace.
[Theorems](../../Silmaril/Containers/SqliteVfs/Completed/Thms.lean)

`blocked_retaining_page` applies the mutation-trace frame to the
projected exchanges. When every exchange is a retaining mutation,
a complete positive-size initial page keeps all of its bytes and
its observed handle mode at the end of the backing trace.
[Mutation trace](sqlite-vfs-mutation-trace.md)

The proofs concern observations of the existing logical container
machine. A caller connecting a native execution must still establish
that its projected event list is an observation of this machine.
The backing trace carries dependent SQLite request and response
values. Native instruction footprints and address mappings are
outside the projection.

```sh
lake build --wfail +Silmaril.Containers.SqliteVfs.Completed.Checks
make check CHECK_TARGETS=+Silmaril.Containers.SqliteVfs.Completed.Checks
```

The kernel checks one completed read followed by a pending receive,
rejects that prefix as blocked, rejects an unmatched send, and recovers
page-byte agreement from a blocked retaining truncate.
[Checks](../../Silmaril/Containers/SqliteVfs/Completed/Checks.lean)
