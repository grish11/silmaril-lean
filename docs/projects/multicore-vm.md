# Finite multicore VM executions

Import `Silmaril.Machine.MulticoreVM.Thms` for the generic interface or
`Silmaril.Machine.MulticoreVM.Toy.Thms` for the runnable register VM. Import
`Silmaril.Machine.MulticoreVM.Placed.Thms` for the layer with explicit core placement
and `Silmaril.Machine.MulticoreVM.Placed.Outcomes.Thms` for the outcome refinement.
[Generic definitions][defs] · [Generic theorems][thms] · [Toy executor][toy] ·
[Placement definitions][placed] · [Placement theorems][placed-thms] · [Outcome refinement][placed-outcomes]

## Scheduling and observations

`Transition` relates a current thread, an auxiliary scheduler choice, and an
initial state to an emitted fragment and a successor state. A fragment can emit
events owned by the current thread, synchronization participant lists, or
nothing. A `Schedule` is a list of thread/choice pairs. The transition
relation can admit several successors for a single pair. An interface that
leaves auxiliary choices to the relation can use `Unit` as its scheduler
choice type.

`run` uses Mathlib's `WriterT` over `SetM`, with `StateT` threading each
branch's state. Every bind appends the next fragment to that branch's word.
`run_eq_iUnion_scheduled` identifies the named outcome set, consisting of
final-state/word pairs, with the union over schedules of exactly the given
length. An unavailable transition contributes no outcome for that branch.
The empty schedule returns the initial state and empty word, and a successful
schedule can stop while more transitions are available.

The pure observation takes the final state. The named observation keeps that
state and the chronological word. The quotient observation keeps the state
and applies `ConcurrentTrace.ofWord` to the word. The trace API supplies
thread-local event and sync projections. [Finite concurrent traces][trace]
`mem_quotient_iff` requires a successful schedule with the same final state
and a word in the given class. Taking the preimage of that class yields its
representatives, with executability established only for the witness word and
schedule. Operational commutation requires a separate proof about the
transition relation. The correspondence covers successful finite prefixes.
Fairness and termination are outside its scope.

## Explicit core placement

`Placed.Config` has separate core and thread IDs and stores. Its placement is a
partial map from present cores to allocated threads, injective on occupied slots.
An allocated thread can wait without a core. When the core ID type is finite,
`Config.resident_card_le_present` bounds the number of resident threads by the
number of configured cores, even when thread IDs are infinite.

An `execute` action names both the core and its resident thread. The instruction
relation may read core state and return an updated valid configuration.
`ofThreadStep` lifts an existing thread-store transition while keeping core state
and placement fixed. For example, a spawn can allocate a waiting child and report
both participants before the child has a core. An `idle` action clears a configured
core. `assign` installs a waiting thread, leaving any displaced thread allocated.
`migrate` moves a resident thread to a configured idle core and leaves its source
idle. All three placement commands preserve both stores and emit the empty word.

`Scheduled.refines` projects any successful finite concrete schedule to a
successful current-thread schedule given `Instruction.Refines`, the per-instruction
obligation on thread stores. The projected execution has the projected final
thread store and the thread word. `Scheduled.mem_threadRun` places the result in
the abstract run at the filtered length, counting every instruction, including
silent ones, and omitting placement commands.

`taggedOutcomes` collects pairs of final configurations and tagged words.
`forgetCore view` applies `StoreView` to the final core and thread stores and
keeps the named thread word. `observeThreadQuotient_image` equates the direct
projection to a final state and thread trace with the image under `forgetCore`
followed by the abstract `observeQuotient`. Under `Instruction.RefinesBy`,
`observeThreadQuotient_image_subset_scheduledOutcomes` and
`observeThreadQuotient_image_subset_run` include this common image in the
abstract quotient outcomes of the projected schedule and the filtered-length
runner, respectively. In the one-core regression, the abstract runner can
execute a waiting child before it is placed, giving strict inclusion for that
concrete schedule. The fixed-schedule inclusion composes with abstract
quotient-outcome equality under the local diamond hypothesis in
`ScheduleEquivalent.quotient_outcomes_eq`. [Abstract scheduler swaps][swaps]

Each emitted letter carries the executing core and thread. `threadWord` recovers
the thread event or the original sync participants. `coreWord` keeps the executing
core and encodes a payload as `some value` and a sync as `none`, an opaque marker on
that core. Both projections commute with fragment concatenation. To descend to a
trace quotient, a projection would have to respect the swaps generating the source
quotient. Two threads time-sharing a core give commuting thread events whose core
images can be dependent. Moving one thread between cores can give the opposite
discrepancy. [Placement regressions][placed-tests]

In the institution adapter, `placedToNamed ≫ namedToConcurrent` agrees with
`Placed.threadTrace` and commutes with typed signature renamings. The separate
`placedToCore` projects to chronological core-local words with opaque sync
markers. [Institution adapter][placed-inst] · [Institution profiles][inst]

## Physical scheduler policies

`Scheduler.CorePolicy` grants an execution opportunity to a present physical
core. Selection leaves the configuration unchanged and may select an idle core.
`Scheduler.ThreadPolicy` decides what to do on that selected core. It can leave
the core idle, keep its resident, assign an unplaced thread (possibly replacing a
resident), or migrate a thread from another core onto the selected idle core.
Every selected thread must be allocated and runnable. Dispatch preserves both
stores and the resulting placement is certified by C8.

An advance executes the dispatched thread using a C8 instruction. The lifecycle
can inspect its fragment and thread states. On a voluntary release or when the
executing thread becomes non-runnable, the advance clears its slot. Otherwise it
preserves placement. A wake can make a waiting thread eligible while it remains
unplaced until an ensuing dispatch.

A scheduling-only round preserves both stores and emits the empty word. An
executing round takes one abstract step, even when the instruction is silent.
`Scheduler.Scheduled.refines` uses C8's `Scheduled.refinesBy` to erase placement
and core attribution while preserving the projected state and named thread word.
The state observation can read both physical stores, and the instruction must
refine the abstract transition under that observation. The abstract run length
counts the executing rounds. These results concern successful finite prefixes
under the supplied policies. [Scheduler API][scheduler]

In the one-core witness, the first thread yields and regains the slot through a
placement-only round, then parks on a matching futex word and releases the slot.
The second thread takes the slot, stores to the shared word and wakes the first.
The wake leaves the waker resident and its recipient eligible but unplaced. A
later dispatch reassigns the slot and the woken thread advances silently. The
six rounds project to five transitions of the keyed wait/wake VM, with the final
shared word and the wake's participant list preserved. [Witness][scheduler-witness]

## Register VM and adapters

A configuration in the original register VM is `ThreadId → Option Core`. Each slot owns a natural-number
register and an instruction list. Addition updates the register silently.
Emit outputs its value. Spawn uses the supplied fresh ID, initializes its
register and program, and emits `sync [parent, child]`. Cores with empty
programs retain their slots. The executable interpreter rejects an unavailable
current thread, a missing or extraneous spawn choice, or an occupied child
slot. `execute_iff_scheduled` relates it to the generic scheduled semantics.

`emit_commutes` checks both schedules when two distinct cores are ready to
emit. The steps consume both instructions and reach the same full
configuration, while the reversed output words have the same quotient.
The regressions also check that a child needs its spawn before it can run,
two fresh ID choices are accepted, and the child's event cannot pass the
spawn marker in the trace quotient. [Toy theorems][toy-thms] · [Regressions][tests]

`machineRuns_iff_exists_schedule` hides the scheduler decisions and uses
`Machine.Trace.Runs` as the finite machine adapter. `Process.Mt` already
models per-thread configurations and spawn, and its SC x86 scheduler chooses
canonical outcomes for some operations. A process adapter would need a
labelled view of its whole-process rules, including a policy for attributing
or separately representing memory-system flushes. The toy VM models local
registers, output, and spawn. [Machine traces][machine] · [Process.Mt][process]

## Checks

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.Machine.MulticoreVM.Regression +Silmaril.Proofs.Semantics.ConcurrentTrace.Regression +Silmaril.Proofs.Machine.MulticoreVM.Placed.Regression +Silmaril.Proofs.Machine.MulticoreVM.Institution.ProjectionRegression'
make check CHECK_TARGETS='+Silmaril.Machine.MulticoreVM.Scheduler.Thms +Silmaril.Proofs.Machine.MulticoreVM.Scheduler.ThreadSyncWitness +Silmaril.Proofs.Machine.MulticoreVM.Placed.Regression +Silmaril.Proofs.Machine.MulticoreVM.ThreadSync.Regression +Silmaril.Proofs.Machine.MulticoreVM.Regression +Silmaril.Proofs.Semantics.ConcurrentTrace.Regression'
```

[defs]: ../../Silmaril/Machine/MulticoreVM/Defs.lean
[thms]: ../../Silmaril/Machine/MulticoreVM/Thms.lean
[placed]: ../../Silmaril/Machine/MulticoreVM/Placed/Defs.lean
[placed-thms]: ../../Silmaril/Machine/MulticoreVM/Placed/Thms.lean
[placed-outcomes]: ../../Silmaril/Machine/MulticoreVM/Placed/Outcomes/Thms.lean
[placed-tests]: ../../Silmaril/Proofs/Machine/MulticoreVM/Placed/Regression.lean
[placed-inst]: ../../Silmaril/Machine/MulticoreVM/Institution/Placed/Thms.lean
[inst]: multicore-vm-institution.md#natural-observation-projections
[swaps]: multicore-vm-swaps.md
[scheduler]: ../../Silmaril/Machine/MulticoreVM/Scheduler/Thms.lean
[scheduler-witness]: ../../Silmaril/Proofs/Machine/MulticoreVM/Scheduler/ThreadSyncWitness.lean
[toy]: ../../Silmaril/Machine/MulticoreVM/Toy/Defs.lean
[toy-thms]: ../../Silmaril/Machine/MulticoreVM/Toy/Thms.lean
[tests]: ../../Silmaril/Proofs/Machine/MulticoreVM/Regression.lean
[trace]: concurrent-traces.md
[machine]: ../../Silmaril/Machine/Trace.lean
[process]: ../../Silmaril/Process/Mt/Defs.lean
