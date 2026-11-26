# Keyed thread synchronization

Import `Silmaril.Machine.MulticoreVM.ThreadSync.Thms`. The adapter uses the
current-thread interface from [#3806][vm-pr] and parameterizes the thread ID,
key, word, local state, and local output types. A `Program` supplies the next
`Action` from the selected thread's ID and local state. `Config.words` is a
shared word map. `Config.threads` maps IDs to optional runnable or parked
slots. A runnable thread can step when its program supplies an action.
[Definitions][defs] · [Theorems][thms]

## Step and event contract

Each step takes a thread ID and a list of wake recipients. Supply an empty
list for local actions, store, wait, and yield. A local action advances the
thread and may emit a local output. A store changes one shared word.

A wait reads its keyed word and commits one of two outcomes atomically. If
the word matches, the thread parks on the key with its saved wake
continuation and emits `waitPark`. Otherwise it advances to a runnable
mismatch continuation and emits `waitMismatch` with the expected and actual
words. A parked thread cannot take any action. A store leaves parked slots
alone.

A wake accepts a list of distinct threads already parked on the wake key, up
to the requested limit. The choice can be any such list, including an empty
list, with no FIFO or maximality policy. Invalid choices have no transition.
Each selected thread becomes runnable at its saved continuation, and the
waker receives the number selected. The named `wake` event carries the
waker, key, limit, and actual recipient list. A nonempty wake also emits a
`sync` marker with the waker first, followed by the selected threads in
choice order. An empty wake leaves future waits unaffected. There are no
wake tokens.

## Dispatch policy

`exec` and `step` leave each thread selection to the caller. Yield advances
the yielding thread's local state, leaves it runnable, and emits `yield` as
an explicit dispatch point. A scheduler can interpret this event using its
own dispatch state.

`cooperativeExec` and `cooperativeStep` supply one policy for a single
dispatcher. Start with `DispatchState.owner = none`. After dispatch, the
owner continues across ordinary actions while it is runnable and has a next
action. Yield, parking, and exhausting the program release ownership. The
following decision may select any runnable thread with a next action,
including the yielding thread. This policy guarantees neither a switch nor
fairness. A model with multiple dispatchers can reuse `exec` or `step` and
maintain dispatcher assignments in its own state.

## Finite runs

`mem_run_iff_execute` specializes #3806's run theorem. The named
nondeterministic outcomes of length `n` are exactly the full final states
and chronological words obtained by successfully executing schedules of
length `n`. The same generic schedule correspondence applies directly to
`cooperativeStep` via `MulticoreVM.mem_run_iff_exists_schedule`.
[Current-thread VM guide][vm]

The regression runs a matching wait on key `7` at word `0`, a store of
`1`, a wake of that waiter, and the resumed local action. Its alternate
store-first schedule takes the mismatch continuation. The model covers
atomic interleaving steps over one shared word map. Linux futex ABI details,
weak memory, and operational commutation of shared updates are outside this
model. In particular, distinct thread names in the trace quotient do not
establish that a store and a wait at the same key can be exchanged.
[Regressions][regression]

```sh
make check CHECK_TARGETS='+Silmaril.Machine.MulticoreVM.ThreadSync.Thms +Silmaril.Proofs.Machine.MulticoreVM.ThreadSync.Regression +Silmaril.Proofs.Machine.MulticoreVM.Regression'
```

[vm-pr]: https://github.com/hiloopai/silmaril-lean/pull/3806
[vm]: multicore-vm.md
[defs]: ../../Silmaril/Machine/MulticoreVM/ThreadSync/Defs.lean
[thms]: ../../Silmaril/Machine/MulticoreVM/ThreadSync/Thms.lean
[regression]: ../../Silmaril/Proofs/Machine/MulticoreVM/ThreadSync/Regression.lean
