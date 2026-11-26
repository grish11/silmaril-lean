# Finite multicore VM executions

Import `Silmaril.Machine.MulticoreVM.Thms` for the generic interface or
`Silmaril.Machine.MulticoreVM.Toy.Thms` for the runnable register VM.
[Generic definitions][defs] · [Generic theorems][thms] · [Toy executor][toy]

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

## Register VM and adapters

A configuration is `ThreadId → Option Core`. Each core owns a natural-number
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
make check CHECK_TARGETS='+Silmaril.Machine.MulticoreVM.Toy.Thms +Silmaril.Proofs.Machine.MulticoreVM.Regression +Silmaril.Proofs.Semantics.ConcurrentTrace.Regression'
```

[defs]: ../../Silmaril/Machine/MulticoreVM/Defs.lean
[thms]: ../../Silmaril/Machine/MulticoreVM/Thms.lean
[toy]: ../../Silmaril/Machine/MulticoreVM/Toy/Defs.lean
[toy-thms]: ../../Silmaril/Machine/MulticoreVM/Toy/Thms.lean
[tests]: ../../Silmaril/Proofs/Machine/MulticoreVM/Regression.lean
[trace]: concurrent-traces.md
[machine]: ../../Silmaril/Machine/Trace.lean
[process]: ../../Silmaril/Process/Mt/Defs.lean
