# Track A concurrency foundations

Import `Silmaril.Semantics.TrackA.Concurrency.Thms` for the full interface.
`Silmaril.Semantics.TrackA.Concurrency.Defs` defines the machine and
`Silmaril.Semantics.TrackA.Concurrency.Race` defines trace classification.
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

The raw generator makes no race check. `ClassifiedRun` reports the clean or
racy label for a generated trace. `FilteredRun` retains clean executions.
`GuardedRun` checks every extension online. Its ordinary observations equal
the filtered executions with the same trace and endpoint. `RaceUB` records
the first racing extension and exposes the attempted trace. Every such UB
has a raw witness, and every raw racy execution contains a UB prefix.
`RaceSafe` quantifies over all schedules. A program with a retained clean
schedule can still reach UB along another schedule. There is no arbitrary
post-UB behavior in this model.

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
semantics. Projection operators are a separate development. Consumers can
use `Event`, `Action`, `sc.MTr`, `ClassifiedRun`, `FilteredRun` and `RaceUB`
to state projections over the same finite histories.

```sh
lake build --wfail +Silmaril.Semantics.TrackA.Concurrency.Thms \
  +Silmaril.Proofs.Semantics.TrackA.Concurrency.Examples
make check CHECK_TARGETS='+Silmaril.Semantics.TrackA.Concurrency.Thms +Silmaril.Proofs.Semantics.TrackA.Concurrency.Examples'
```

- Leslie Lamport, *How to Make a Multiprocessor Computer That Correctly
  Executes Multiprocess Programs*, 1979. [DOI](https://doi.org/10.1109/TC.1979.1675439)
- Maurice Herlihy and Jeannette Wing, *Linearizability: A Correctness
  Condition for Concurrent Objects*, 1990. [DOI](https://doi.org/10.1145/78969.78972)
