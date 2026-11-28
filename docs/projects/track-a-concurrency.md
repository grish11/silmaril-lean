# Track A concurrency foundations

Import `Silmaril.Semantics.TrackA.Concurrency.Thms` for the full interface.
`Silmaril.Semantics.TrackA.Concurrency.Defs` defines the machine and trace
classification. The earlier `Silmaril.Semantics.TrackA.Concurrency.Race`
import re-exports that header.
The modules use the root project's pinned Lean and CSLib. The latter supplies
the labelled transition system and finite execution relation. The model and
proofs are independent of the SQLite and ELF implementation modules.

## Executions and observations

A program uses natural-valued cells and fixed types of thread, resource and
lock identifiers. A load reads the current cell and passes its value to the
thread's continuation. A store updates one cell. Each primitive is one SC
transition and emits one `Event`, carrying a thread and an `Action`. A trace is
the ordered list of those events. `sc.MTr` relates the initial configuration,
trace and final configuration. `replay_iff` relates this execution to replay of
the exact schedule obtained from the thread labels. `single_run_iff` recovers
the sequential semantics when the thread type is `Unit`.

A mutex stores one optional owner. Use `Unit` as the lock type for a single
mutex and any discrete identifier type for indexed mutexes. Acquire requires
an empty owner slot and release requires the caller to own that slot.
`Config.Held` and `Config.Waiting` expose ownership and pending blocked
acquires. A blocked acquire emits no event, including on self-acquire.
`Config.Stuck` is finite terminality with unfinished code.
`Config.LockCycle₂` records a two-thread wait cycle, which can coexist with
running peers in a larger configuration. The checked two-thread example is
globally stuck.

## Races

A conflict is a pair of memory accesses by different threads to the same
resource with at least one write. Happens-before is the nonempty transitive
closure of forward event edges. These include same-thread program order and
release-to-acquire edges for the same mutex. All ordering and classification
operate on event positions so repeated labels stay distinct.

The mutex-only profile treats every memory access as ordinary. The mixed
profile gives SC atomic stores and loads release/acquire synchronization
when the load reads from the store. A write between them to the same
resource, including a plain write of the same value, breaks that reads-from
edge. Two atomic accesses are exempt in the mixed profile. A pair containing
a plain access can still race. Every mixed-profile race is also a
mutex-only race on the same trace.

`classify` and `atomicSync` are total tests of labels and positions. They
can report a clean list or identify a candidate atomic edge even if a
recorded read contradicts the last preceding write. Interpreting that edge
as SC reads-from requires the actual labels at those positions in a
generated SC execution. `classifyHistory` replays the thread schedule
from a specified initial configuration and checks every emitted label.
Its result is `none` for an inadmissible list. The theorem
`classifyHistory_eq_some_iff` relates successful results exactly to
`ClassifiedRun`. The regression for a forged atomic read checks rejection
even though the raw mixed classifier reports clean.

The raw generator makes no race check. `ClassifiedRun` reports the clean or
racy label for a generated trace. `FilteredRun` retains clean executions.
`GuardedRun` checks every extension online. Its ordinary observations equal
the filtered executions with the same trace and endpoint. `RaceUB` records
the first racing extension and exposes the attempted trace. Every such UB
has a raw witness, and every raw racy execution contains a UB prefix.
`RaceSafe` quantifies over all schedules. A program with a retained clean
schedule can still reach UB along another schedule. There is no arbitrary
post-UB behavior in this model.

## Interface observations

Import `Silmaril.Semantics.TrackA.Concurrency.Projection.Thms` for interface
projection. An `Interface` exposes selected resources and mutexes. Its
`observe` function filters a finite history while keeping each visible event's
thread, operation and value. `Interface.projection` maps each visible
position to its original occurrence in strictly increasing order. This
distinguishes repeated labels and preserves conflicts, access modes and
mutex synchronization between retained events.

`Interface.ObservedRun` supplies a source `sc.MTr` witness with the same
initial and final configurations. `Interface.observedRun_inter` factors
restriction through an intermediate observation of that execution.
`Projection.comp` composes the occurrence maps. A filtered history is used
as an observation of the source execution. The factorization concerns
finite traces and their source endpoints. It gives no guarantee about
executability of the filtered history, schedules, fairness or atomicity
of multi-step operations.

For retained pairs, there are two separate comparisons.

| Sufficient condition | Happens-before | Races |
| --- | --- | --- |
| `Projection.CoversOverwrites` in the mixed profile | Observed paths lift to the source | Retained source races remain visible |
| `Projection.KeepsCrossThreadEdges` | Source paths remain ordered between retained endpoints | Visible races reflect source races |

`Projection.atomicSync_eq` compares the raw `atomicSync` Boolean on
retained action labels under overwrite coverage. The Boolean tests for an
atomic write and read on the same resource and checks the intervening
slice for overwrites. Interpreting `true` as reads-from requires positions
`i < j` in a history generated by `sc.MTr`. The `direct` predicate checks
index order.

For the first direction, `Projection.direct_eq` compares retained direct
edges. An overwrite of the same resource between a candidate atomic write
and read must have a visible witness whenever the source has one. A plain
write or a write of the same value still counts. The mutex-only profile
requires no overwrite condition. For the other direction, every cross-thread
direct edge keeps both endpoints. The proof compresses stretches of
same-thread program order through hidden occurrences between the retained
endpoints.

`Interface.CoversSynchronization` gives a concrete sufficient condition
for both directions. Expose every mutex used in the trace and, in the
mixed profile, every resource accessed atomically. This also retains
plain overwrites of those resources and allows hiding plain accesses on
other resources. `Interface.racePair_eq` then compares any retained pair.
`Projection.hasRace_to_source` reflects an observed whole-trace race
under the cross-thread condition. The converse `hasRace_to_observed`
also asks for `Projection.CoversConflicts`, so a source race still has
both endpoints in the observation. Together these conditions give
`Projection.classify_eq`.

## Checked examples and limits

The examples check both disjoint-store orders, a protected increment, a
two-mutex deadlock and a completing schedule for the same code, mixed
publication and overwrite, and a lost update using only SC atomic loads and
stores. The protected increment is race-free on every reachable prefix.
Every completed execution gives the serial value and releases the mutex.
The examples also enumerate both complete schedules. The unprotected race-free execution has final value 1 where both
serial orders of the two calls give 2. The comparison concerns an observable
final cell for these specific calls. General call histories, real-time
ordering and linearizability proofs are outside this development.

The model covers finite executions without scheduler fairness or starvation
guarantees. It leaves out allocation, byte overlap, weak memory, read-modify-write
primitives, condition variables, reentrant mutexes, and the C and SQLite
semantics.

The projection examples use checked raw SC schedules. Hiding the mutex
handoff makes two retained plain writes appear to race. Hiding an
intervening atomic write of the same value fabricates a reads-from edge
and suppresses a race between retained payload accesses. A third example
exposes the whole atomic resource while hiding the plain payload resource.
Its observed trace is clean even though the source is racy. An occurrence
example checks that identical visible labels map to distinct source positions.

```sh
targets='+Silmaril.Semantics.TrackA.Concurrency.Thms +Silmaril.Proofs.Semantics.TrackA.Concurrency.Examples +Silmaril.Semantics.TrackA.Concurrency.Projection.Thms +Silmaril.Proofs.Semantics.TrackA.Concurrency.Projection.Examples'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env leanchecker Silmaril.Semantics.TrackA.Concurrency.Projection.Thms
lake env leanchecker Silmaril.Proofs.Semantics.TrackA.Concurrency.Projection.Examples
SILMARIL_REPLAY_MODULE=Silmaril.Proofs.Semantics.TrackA.Concurrency.Projection \
  lake env lean tools/compiler-explorer/Replay.lean
```

- Leslie Lamport, *How to Make a Multiprocessor Computer That Correctly
  Executes Multiprocess Programs*, published version, IEEE Transactions on
  Computers C-28(9), September 1979, p. 690, Introduction (definition of
  sequential consistency). Author-hosted PDF SHA-256
  `defa8b352a0cefc1bf29ea653bef9d48da4e3e5aff1b7e7c4f10d7c933949ffe`.
  [DOI](https://doi.org/10.1109/TC.1979.1675439) · [PDF](https://lamport.azurewebsites.net/pubs/multi.pdf)
- Maurice Herlihy and Jeannette Wing, *Linearizability: A Correctness
  Condition for Concurrent Objects*, published version, ACM Transactions on
  Programming Languages and Systems 12(3), July 1990, §2.2, pp. 468–469
  (history and real-time order). Author-hosted PDF SHA-256
  `79e2ff81a15c55de870492231e81e36c50366389c118a7317b5877f603cfa2a0`.
  [DOI](https://doi.org/10.1145/78969.78972) · [PDF](https://cs.brown.edu/~mph/HerlihyW90/p463-herlihy.pdf)
