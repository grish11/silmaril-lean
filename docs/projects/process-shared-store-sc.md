# Process ITree and Brookes SC on the shared-store fragment

Import `Silmaril.Process.ITreeTrace.SharedStore.Thms`. The fragment is TreeSC's
lock-free `Code R` over a shared `R → Nat` store. It includes reads with
reply-dependent continuations and writes to one cell. Thread and cell identifiers
have decidable equality. A pool assigns one fixed program to each thread and
successful threads return `Unit`. [Definitions][defs] · [Theorems][thms]

## Call boundaries and observations

The adapter presents TreeSC's existing typed read and write requests through
`TypedSyscall.Signature`. The shared-store kernel completes each selected call
atomically. A read replies with the value at its pre-store and leaves the store
intact. A write commits one update and replies with unit. There is one completion
per request at every store. The fragment admits no blocking, faults, process exit,
locks, or thread creation. This kernel specifies the linearization point at the
call transition. Using the same result for a concrete syscall would require a
separate simulation that discharges this atomic call contract. [Typed process
boundary][typed] · [TreeSC frames][frames]

The raw label is a TreeSC frame with the operation, its dependent reply and the
stores at both sides of the call. `Completes` projects that frame with
`Frame.event`, preserving thread, access mode, cell, and the read or written
value in order. Per-call store snapshots are hidden by the event projection.
The theorem keeps the exact initial and final stores and requires all threads to
return. Both access modes follow Track A's raw SC primitives. Race classification
is outside this comparison. [Process scheduling][flatten] · [Track A SC][sc]

## Scheduling and interference

`completes_iff_sc` compares completed finite process interleavings with the
same multi-step relation used by TreeSC. `replay_of_completes` deletes selections
of returned threads and the unused schedule suffix by taking the thread ID of
each emitted event and proves that they form a subsequence of the supplied
schedule. `completes_of_replay` takes a successful SC replay that ends
with every thread done and uses its schedule directly. A read or an idempotent
write is still an event, even when its store transition is an identity. An empty
schedule completes only when all threads are already done. The condition is
finite progress to all returns. There is no fairness assumption or conclusion
about infinite schedules or an exhausted prefix. Weak ITrees expose calls and
returns without recording finite internal steps. [Schedule law][thms]

The SC store changes only through scheduled calls. Other modeled threads may
intervene between calls and supply the next read's pre-store. There are no
additional environment steps. `singleton_completes_iff_denote` hides the schedule
and full event word and recovers TreeSC's saturated Brookes denotation at its
closed endpoint observation. In the open Brookes language, gaps can admit
external interference, stuttering can insert identity transitions, and mumbling
can contract contiguous transitions. These deductions do not change which calls
are reported in the raw schedule law. The operational comparison reuses the existing
SC scheduler. For two threads indexed by `Bool`, `parallel_completes_of_completes`
uses the existing `Behavior.parallel` to admit each completed process run at
its exact store endpoints and unit result pair. The proof extends the selected
thread's store-pair word at each call and keeps the shuffle contiguous across
threads. The comparison to saturated parallel is an inclusion of closed
endpoint observations. Its converse and a comparison of open trace languages
remain outside this result. [Closed TreeSC][closed] · [Brookes
parallel][parallel]

## Running the example

```sh
lake build --wfail +Silmaril.Process.ITreeTrace.SharedStore.Thms \
  +Silmaril.Proofs.Process.ITreeTrace.SharedStore.Examples
lake env lean -DautoImplicit=false -DwarningAsError=true \
  Silmaril/Proofs/Process/ITreeTrace/SharedStore/Examples.lean
```

The example checks two schedules for a writer and a thread that reads and copies
its reply into another cell. The read reply and copied value are both `7` when
the writer runs first and both `0` when the read runs first. The example runs
Track A's executable replay and checks the corresponding process observations
in Lean, including a skipped writer selection and both closed Brookes parallel
endpoints. [Examples][examples]

[defs]: ../../Silmaril/Process/ITreeTrace/SharedStore/Defs.lean
[thms]: ../../Silmaril/Process/ITreeTrace/SharedStore/Thms.lean
[examples]: ../../Silmaril/Proofs/Process/ITreeTrace/SharedStore/Examples.lean
[typed]: ../../Silmaril/Process/TypedSyscall/Defs.lean
[frames]: ../../Silmaril/Semantics/Brookes/TreeSC/Defs.lean
[flatten]: ../../Silmaril/Process/ITreeTrace/Defs.lean
[sc]: ../../Silmaril/Semantics/TrackA/Concurrency/Defs.lean
[closed]: brookes-tree-sc-closed.md
[parallel]: ../../Silmaril/Semantics/Brookes/Parallel/Thms.lean
