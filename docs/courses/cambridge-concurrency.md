# Shared-store concurrency in Cambridge L1

This development follows chapter 7, pp. 89–97, of Peter Sewell's
*Semantics of Programming Languages*, Cambridge Part IB, dated 12 February 2026. The syllabus on p. 3 names shared-variable interleaving,
simple mutexes, and serializability. The source digest is recorded under
`sewell2026semantics` in the bibliography. [Course notes](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=89) · [Bibliography](../../references.bib)

```sh
lake build --wfail Silmaril.Courses.Cambridge.Concurrency.Course
```

Import `Silmaril.Courses.Cambridge.Concurrency` for the first interleaving
language. The `.Course` module adds metatheory, checked examples, and the
mutex extension. For the mutex language, Theorem 27, and ordered locking, import
`Silmaril.Courses.Cambridge.Concurrency.Mutex.Course`. The separate
`Silmaril.Courses.Cambridge.Concurrency.UnixThreads.Course` import gives the
Exercise 40 extension.

## Rules and checked behavior

`Concurrency.Expr.parallel` extends the L1 expression grammar.
`Concurrency.HasType.thread` views a unit expression as a process, and
`HasType.parallel` composes two processes. The ordinary L1 typing rules
operate over the extended type grammar. For example, sequencing can return
a process on its right-hand side.

`Concurrency.Step.parallelLeft` and `Step.parallelRight` each take one
operand step. Every step sees the same finite store of named integer cells.
Reading a cell and writing an integer each take one step. An expression
such as an increment may take several steps, which can interleave with
the other thread. When all threads finish, the expression is a parallel
tree of `skip` leaves and the configuration is terminal.

The reductions in `Concurrency.Examples` witness both final stores from the
two writes on p. 90. For the p. 91 race that adds 1 and 7 to a cell initially
holding 0, checked schedules reach 1 and 7 when both threads read the initial
value, and 8 when a thread reads the other's write. The derivations identify
concrete finite schedules and their final stores.

| Result | Public name in `Silmaril.Courses.Cambridge.Concurrency` |
| --- | --- |
| Sequential L1 typing and reduction embed | `HasType.ofL1`, `Step.ofL1` |
| Completed processes are terminal | `ProcessDone.terminal` |
| Every typed configuration with a covering store is complete or can step | `progress` |
| Every step preserves its source type and the store domain | `preservation`, `Step.store_domain` |
| Progress holds at every configuration reached by a finite trace | `safety` |

## Primitive mutexes and labelled steps

The mutex extension carries a shared Boolean for each mutex alongside
the finite integer store. In `Mutex.Step`, `lock` checks for `false` and
sets the bit to `true` in a single step. `unlock` sets it to `false` and
can step even when the bit is already `false`. Both commands have type
`unit`.

`Mutex.ThreadStep` describes the expression-side transition and its label.
The five labels distinguish internal computation, a write, a read with a
proposed result, acquisition, and release. `Mutex.Effect` checks the state
premises and applies the action. A local read can propose any integer.
The global configuration rule accepts the proposal when it matches the
current cell. Likewise, a local lock transition can propose an acquisition
when the corresponding global command has to wait.

| Result | Public name under `Silmaril.Courses.Cambridge.Concurrency.Mutex` |
| --- | --- |
| The global and labelled presentations coincide on all configurations (Theorem 27) | `step_iff_labelledStep` |
| Reductions preserve typing and store coverage | `preservation` |
| Interleaving typing and reduction embed | `HasType.ofInterleaving`, `Step.ofInterleaving` |
| A held mutex blocks a global lock step | `lock_terminal` |

The examples check the seven local actions of the guarded increment on p. 95
and the two-lock deadlock on p. 93. The deadlock reaches a terminal
configuration with both acquisitions still pending. The same expression
has type `proc` under the two location declarations.

### Exercise 37 and the C&DS comparison

The 2025–26 C&DS slides describe a read-and-set acquisition loop and a
clear operation. `Mutex.Comparison.acquire_iff` and `release_iff` prove
that successful operations on this bit are exactly the projections of
the SPL lock and unlock steps onto the selected mutex. Both release
rules clear the bit from either prior state. On a held lock,
`held_attempts` checks the C&DS retry and failed `trylock` outcomes
alongside the blocked SPL command. [Read-and-set, lecture 1 slide 33](https://www.cl.cam.ac.uk/teaching/2526/ConcDisSys/conc-sys-slides.pdf#page=33) · [POSIX example, lecture 4 slide 23](https://www.cl.cam.ac.uk/teaching/2526/ConcDisSys/conc-sys-slides.pdf#page=96)

The comparison projects to one Boolean. C&DS uses a spin loop for the
read-and-set implementation and also presents blocking POSIX acquisition
and a nonblocking `trylock` call. The Java example permits reentry by the
same thread. SPL instead has an actor-independent test of the held bit,
so the same waiting rule applies to every acquisition of a held mutex.
The pinned slide deck is recorded as `cambridge2025concurrent` in the
bibliography. [Java example, lecture 4 slide 27](https://www.cl.cam.ac.uk/teaching/2526/ConcDisSys/conc-sys-slides.pdf#page=100) · [Bibliography](../../references.bib)

## Ordered two-phase locking

`Mutex.OrderedTwoPhase.Layout` fixes a bijection from locations to mutex
names and a total acquisition order. `Obeys` checks every finite labelled
history of a thread. Each memory access requires its mutex to be held.
Acquisitions and releases alternate per mutex, all acquisitions precede
all releases, and acquisitions follow the fixed order. A terminal local
thread must have released every mutex. `Obeys.infinite_prefix` proves that
the same four event conditions hold at every finite prefix of an infinite
thread execution.

`Conjecture28` is the proposition for the printed statement. The threads
have type `unit` under a shared location environment, as set out on p. 93.
The comparison uses right-associated parallel and serial composition, an
initially available mutex state, and every initial store. A terminal
parallel state is serializable if any prefix of a permutation's serial
execution reproduces its whole shared state. A terminal global state
with a pending local lock action violates deadlock freedom.

The pinned text calls this Conjecture 28 and warns that it may be false.
`Examples.conjecture28_false` refutes the literal quantification over
every initial store. Two typed threads satisfy all the discipline
conditions. With an empty store, one acquires the mutex and blocks on
a write to an absent cell. The other thread still proposes a lock at
the terminal global state. `CoveredConjecture28` separately requires
the initial store to cover the location environment, as in the course's
L1 progress theorem. That variant remains open in this development.

### Exercise 38

The four examples use covering stores. Each proof checks the retained
conditions over all local traces of the fixture and witnesses the
failure when the indicated condition is dropped.

| Dropped condition | Checked result |
| --- | --- |
| Protect each memory access | `protection_necessary` shows that opposite write orders can produce a mixed result absent from both serial prefix sets. |
| Match releases at termination | `terminal_release_necessary` shows a thread finishing with its lock held and blocking another thread. The per-mutex prefix alternation still holds. |
| Complete acquisitions before releasing | `two_phase_necessary` shows a nonserializable three-cell result even though each access is protected and the locks are acquired in order. |
| Acquire locks in increasing order | `increasing_order_necessary` shows the two opposing lock orders deadlocking. |

## Exercise 40 and Unix-style threads

`UnixThreads.Command` combines L1 commands with lightweight thread
creation, join, and asynchronous integer channels. This is a design for
the exercise. The first thread has ID 0. `fork` creates a thread with
the next fresh ID, puts that ID into a shared integer cell, and resumes
the parent. `join` reads an ID from such a cell and waits for that
thread's completion. A successful join removes the completed thread.

All threads use the same finite L1 store. An ordinary command follows
`L1.Step` until it produces `skip`. A send reads a shared cell and appends
its integer to a named FIFO. A receive waits for a queued integer, takes
the head, and writes it to an allocated cell. A global step is labelled
with the chosen thread's ID. This models an abstract thread scheduler
and unbounded queues for the exercise. [Thread IDs and join, C&DS lecture 1 slide 12](https://www.cl.cam.ac.uk/teaching/2526/ConcDisSys/conc-sys-slides.pdf#page=12) · [Asynchronous messaging, lecture 6 slide 10](https://www.cl.cam.ac.uk/teaching/2526/ConcDisSys/conc-sys-slides.pdf#page=144)

`Step.preserves_wellFormed` and `trace_preserves_wellFormed` preserve
command typing, store coverage, and the bound on allocated IDs. The
counter is monotone. `receive_waits` and `join_waits` give the corresponding
blocking conditions for a scheduled thread. The checked fork/send/receive/join
trace transfers a value computed by an L1 child command and reaps the child.
A separate trace checks FIFO order on two queued integers.

## Chapter 7 coverage

| Syllabus item | Notes | Coverage |
| --- | --- | --- |
| Shared-variable interleaving | pp. 89–91 and p. 97 | Global steps over one store, race derivations, progress, preservation and finite-trace safety |
| Simple mutexes | pp. 92–93 | Boolean mutex state, direct rules, typing, blocking and the two-lock deadlock |
| Thread-local labelled semantics | pp. 94–96, Theorem 27 | Labelled expression steps and state effects, with a proof of coincidence with the global rules |
| Ordered two-phase locking | p. 97 | Trace discipline, serializability and deadlock freedom defined in Lean |
| Exercise 37 | §7.1, p. 97 | Bit-level lock and unlock correspondence with the pinned C&DS slides, plus the checked retry, nonblocking attempt, and SPL waiting distinction. |
| Exercise 38 | §7.1, p. 97 | All four necessity examples are checked, including every serial prefix in the serializability cases. |
| Exercise 39 | §7.1, p. 97 | Counterexample for the printed store quantifier. The covered-store variant remains open here. |
| Exercise 40 | §7.1, p. 97 | Unix-style identified threads with fork and join, shared memory and asynchronous FIFO channels, with preservation and checked traces. |

The interleaving semantics allows any enabled scheduling choice.
