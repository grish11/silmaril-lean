# Read and write observations

A read event records an address and a value. A write event records an address
and its replacement value. The read and write projections retain their values,
order and repetitions. For one address, `Trace.ConsecutiveReads` selects two
reads with no intervening read at that address. Its gap can contain writes and
accesses at other addresses. `lastWrite` selects the final write to the address
in the gap, if present. [Definitions](../../Silmaril/Semantics/ReadWrite/Observations/Defs.lean)

| Rule for consecutive reads | Required value of the later read |
| --- | --- |
| `ReadsStable` | The earlier value, across every gap. |
| `ReadsStableWithoutWrites` | The earlier value when the gap contains no write to that address. A gap with a relevant write allows any value. |
| `ReadsMatchLastWrite` | The value of the last relevant write, or the earlier value when there was no relevant write. |

The gap predicates hold vacuously for zero or one read. Their address sets
require a pair of reads. `StableReadAddresses` and `ChangedReadAddresses`
partition `RepeatedReadAddresses`. Both `StableReadAddresses` and
`LastWriteCompatibleAddresses` are subsets of `StableWithoutWritesAddresses`.
The permissive rule “a change requires some intervening write” is equivalent
to equality across write-free gaps. A changed read that matches the last write
can satisfy that rule and fail unconditional equality. A stale read that
repeats the earlier value after a different write can satisfy unconditional
equality and the permissive rule while failing last-write compatibility.
[Implication and partition laws](../../Silmaril/Semantics/ReadWrite/Observations/Thms.lean)

Replay implies equality across write-free gaps when successful writes preserve
reads at other addresses. Last-write compatibility also uses
`Access.ReadsAfterWrite`. This law determines the value of a successful read
at the address just written and permits a backend to reject reads there.
For a compatible pair, the later observation differs exactly when a last
write exists and assigns a value different from the earlier read. Writing the
earlier value therefore preserves the observation, including when an earlier
write in the same gap assigned a different value. The repeated-read rules
inspect only pairs, so replay also checks every first read, access permissions
and bounds independently. [Replay laws](../../Silmaril/Semantics/ReadWrite/Observations/Thms.lean)

## Removing accesses

Removing reads from a successful mixed replay preserves both endpoints.
The write projection by itself checks writes and cannot validate the original
read observations. Removing writes preserves the recorded observations as
data, including equality and repetition, while discarding the intervening writes
that can explain changes.

The read projection is a replay on one unchanged snapshot exactly when all its
values match that snapshot. After a successful mixed replay with the two
backend laws, `Replays.reads_agree_iff` tests this on the initial snapshot by
checking the last write before each read that has one. Reads with no preceding
write to their address already match the initial state by locality. Disjoint
read and write addresses suffice. A same-value write or restoration before a
read can also preserve replay of the projection. Equal repeated observations
alone cannot ensure this, since a write before the first read can supply a
different value or initialize backing. [Projection and replay laws](../../Silmaril/Semantics/ReadWrite/Observations/Thms.lean)

## Process memory and page arrays

`Memory.readProjection` and `Memory.writeProjection` produce distinct
`ByteReadTrace` and `ByteWriteTrace` types. Each has `run`, `Replays` and
`toTrace`. Read-only replay returns the initial memory and checks read
permission and backing at every observation. Write-only replay requires all
assignments to be permitted by the initial mapping, applies assignments in
order, and can fill missing backing. Its `WritesWithin` frame preserves the
entire mapping and all backing bytes outside the assignment addresses.
Writing a byte in a write-only mapping leaves reads there forbidden.
Each event touches one byte and uses the ordinary checked memory operations.
[Memory API](../../Silmaril/Process/Memory/Trace/Projections/Thms.lean) · [Memory checks](../../Silmaril/Process/Memory/Trace/Projections/Checks.lean)

Total and optionally initialized page arrays both satisfy the locality and
read-after-write laws. The latter can initialize an allocated page by writing
it. The examples cover same-value writes, changed observations, restoration,
stale reads, and an out-of-bounds read.
[Page array API](../../Silmaril/Semantics/Page/Array/Observations/Thms.lean) · [Page array checks](../../Silmaril/Semantics/Page/Array/Observations/Checks.lean)

```sh
lake build --wfail +Silmaril.Process.Memory.Trace.Projections.Checks \
  +Silmaril.Semantics.Page.Array.Observations.Checks
```
