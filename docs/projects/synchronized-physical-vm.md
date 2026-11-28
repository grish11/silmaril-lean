# Synchronized physical register VM

Import `Silmaril.Machine.MulticoreVM.Synchronized.Physical.Thms` for the
physical scheduler instantiation or
`Silmaril.Machine.MulticoreVM.Synchronized.Legacy.Thms` for compatibility with
the old add, emit, and spawn fragment.

## Enlarged current-thread VM

`Synchronized.exec` preserves the register VM's add, emit, and fresh-child
spawn operations. It delegates local instructions and keyed synchronization to
`ThreadSync.exec`. The spawn choice supplies a fresh thread ID. Other choices
supply a wake list, which is empty for operations other than wake.

A matching wait parks the caller with its saved continuation. Mismatch
continues immediately with register value one, and wake resumes with value zero.
A wake sets the waker's register to the number of parked waiters selected by
that step and emits the participant marker for a nonempty wake. Yield advances
the current thread to its next instruction and emits a yield event.
[Current-thread definitions][vm] · [Thread synchronization][thread-sync]

## Old-fragment compatibility

`Legacy.exec_embed` and `Legacy.execute_embed` are exact equalities for the old
programs and choices, including rejected executions. The embedding recursively
translates spawned programs, wraps numeric outputs as local-output events, and
preserves synchronization participant lists. Shared words are arbitrary and
remain unchanged throughout an embedded legacy run. `Legacy.placed_refines`
first applies the original C8 projection to a legacy physical execution and
then embeds its current-thread result. [Legacy compatibility theorems][legacy]

## Physical refinement

A distinguished configured physical slot stores the shared word map. Any core
can execute through that map, and writeback preserves every other core's local
store. The scheduler chooses a present core and independently dispatches a
runnable thread to it. A freshly spawned child is allocated and unplaced.
Yield, parking, or exhaustion clears the executing slot. A wake can restore
eligibility while the recipient stays unplaced until a later dispatch.

`Physical.Scheduled.refines` projects a successful physical schedule to the
enlarged current-thread VM, preserving the shared word map, thread store, and
named word. It reuses the C8 schedule and word erasures through the separately
imported `Placed.StoreProjection.Thms` extension. Placement-only rounds
contribute no abstract step. Silent instructions count toward the abstract run
length. The finite theorem applies to executions admitted by the supplied core
and thread policies. [Physical refinement theorems][physical]

The two-core witness spawns a child, places it in a scheduling-only round, and
parks it on a matching wait. The parent yields on the first slot, then uses the
second slot to store into shared memory and wake the child. The child becomes
eligible while remaining unplaced. It subsequently takes the first slot and
emits. The seven physical rounds project to six current-thread steps and
preserve the shared write and the spawn and wake participants. [Regression][tests]

## Checks

```sh
make check CHECK_TARGETS='+Silmaril.Machine.MulticoreVM.Synchronized.Legacy.Thms +Silmaril.Machine.MulticoreVM.Synchronized.Physical.Thms +Silmaril.Proofs.Machine.MulticoreVM.Synchronized.Regression +Silmaril.Proofs.Machine.MulticoreVM.Scheduler.ThreadSyncWitness +Silmaril.Proofs.Machine.MulticoreVM.Placed.Regression +Silmaril.Proofs.Machine.MulticoreVM.ThreadSync.Regression +Silmaril.Proofs.Machine.MulticoreVM.Regression +Silmaril.Proofs.Semantics.ConcurrentTrace.Regression'
```

[vm]: ../../Silmaril/Machine/MulticoreVM/Synchronized/Defs.lean
[thread-sync]: multicore-vm-thread-sync.md
[legacy]: ../../Silmaril/Machine/MulticoreVM/Synchronized/Legacy/Thms.lean
[physical]: ../../Silmaril/Machine/MulticoreVM/Synchronized/Physical/Thms.lean
[tests]: ../../Silmaril/Proofs/Machine/MulticoreVM/Synchronized/Regression.lean
