# Free-shuffle parallel composition

Import `Silmaril.Semantics.ConcurrentTrace.Parallel.Thms` to compose sets of
finite [concurrent traces][finite]. The sets themselves may be arbitrary.

`shuffleWords` interleaves word languages, taking one letter occurrence at a
time and preserving the order of each input word. `parallel` shuffles all
representatives of both input trace languages and takes the quotient image.
`shuffle_swap` shows how to exchange adjacent independent output letters.
When their origins differ, both component words are unchanged. When their
origins agree, the exchange performs one legal adjacent swap in that component.
Consequently, shuffling saturated languages is already saturated, and
`ofTraces_parallel` recovers exactly the shuffles of the input representatives.
[Definitions][defs] · [Theorems][thms]

The product is associative and commutative, has unit `{1}` (the singleton
empty trace), and distributes over binary union in both operands.
`mem_parallel_ofWord` tests an output representative against the two sets by
requiring a shuffle whose component words belong to the corresponding traces.
[Theorems][thms]

The components can use the same thread ID. For example, lifting the
one-event words `[2]` and `[3]` into the same thread gives two distinct
possible output orders. Two input synchronization letters contribute two
occurrences even when their participant lists coincide. Handshake composition
would need rules for matching and combining component steps. An operational
interpretation would also have to enforce VM thread-state and shared-effect
constraints. [Lean examples][regression]

A fixed representative can omit an entire output trace. Let `a` and `b`
be events on different threads and let `s` synchronize both threads.
Interleaving `[b,a]` with `[s]` gives `[b,s,a]`. The equivalent left word
`[a,b]` cannot give that trace even after quotienting the output, because the
observations of the two participating threads fix which side of `s` their
events occur on. [Lean examples][regression]

## Checks

```sh
make check CHECK_TARGETS='+Silmaril.Semantics.ConcurrentTrace.Parallel.Thms +Silmaril.Proofs.Semantics.ConcurrentTrace.Parallel.Regression'
```

[finite]: concurrent-traces.md
[defs]: ../../Silmaril/Semantics/ConcurrentTrace/Parallel/Defs.lean
[thms]: ../../Silmaril/Semantics/ConcurrentTrace/Parallel/Thms.lean
[regression]: ../../Silmaril/Proofs/Semantics/ConcurrentTrace/Parallel/Regression.lean
