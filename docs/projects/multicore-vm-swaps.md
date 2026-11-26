# Adjacent decision swaps in the multicore VM

Import `Silmaril.Machine.MulticoreVM.Swaps.Thms` to reason about swaps in the
[finite scheduled semantics](multicore-vm.md). [Definitions][defs] · [Theorems][thms]

`LocalDiamond step state a b` requires replay in both directions. For every
successful execution of `[a, b]`, there must be an execution of `[b, a]` from
the same state to the same final state with the same concurrent trace class.
The reverse direction quantifies over every successful execution of `[b, a]`.
Intermediate states and fragment choices can differ. Use
`scheduleReplay_pair_iff` to prove either direction directly from the two
transition premises. Its trace condition compares the products of the
classes of the two named fragments in execution order.

`adjacent_swap_replay` applies the local diamond at the states reached by a
given schedule prefix from a fixed initial state. The proof reuses the prefix
and suffix executions. Multiplication in the trace monoid preserves equality
when those words are concatenated around the replay.

`scheduleCongruence allowed` is the least concatenation congruence containing
the swaps admitted by an adapter's decision-pair policy. A policy may list a
pair in one order because the local diamond supplies both replay directions.
Prove the diamond at every state for each admitted pair to use
`ScheduleEquivalent.replay` or `ScheduleEquivalent.quotient_outcomes_eq`.
The latter equates sets of pairs of final states and trace classes at every
initial state. These implications run from schedule equivalence to observation
preservation. They cover successful finite runs.

## Register VM example

Import `Silmaril.Machine.MulticoreVM.Toy.Swaps.Thms`. Its
`Toy.emit_localDiamond` specializes the interface to a state with two
distinct cores ready to emit. Each order consumes both instructions, and
the two emitted events commute in the trace quotient. A prefix can justify
this state-specific rule by establishing readiness at its reachable states.
[Toy theorem][toy]

Spawn creates a dependency across distinct thread IDs. A child can emit after
its parent spawns it, and attempting the child decision first is blocked.
Co-enabled steps can also conflict. Two writes to the same shared register can
leave different final values in opposite orders. Even with equal final states,
the concurrent trace records the order of distinct synchronization markers.
An adapter must show both state replay and trace equality for the steps it
admits. [Spawn regressions][spawn]

## Checks

```sh
make check CHECK_TARGETS='+Silmaril.Machine.MulticoreVM.Toy.Swaps.Thms +Silmaril.Proofs.Machine.MulticoreVM.Regression +Silmaril.Proofs.Semantics.ConcurrentTrace.Regression'
```

[defs]: ../../Silmaril/Machine/MulticoreVM/Swaps/Defs.lean
[thms]: ../../Silmaril/Machine/MulticoreVM/Swaps/Thms.lean
[toy]: ../../Silmaril/Machine/MulticoreVM/Toy/Swaps/Thms.lean
[spawn]: ../../Silmaril/Proofs/Machine/MulticoreVM/Regression.lean
