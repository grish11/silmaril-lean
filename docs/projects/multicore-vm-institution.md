# Finite trace tests for multicore VMs

Import `Silmaril.Machine.MulticoreVM.Institution.Thms` for the typed signatures,
observation profiles and institution. The construction uses Silmaril's rooms
and corridors and exports a `ClassicInstitution` in the sense of
Goguen and Burstall (1992, §2.1, Definition 1).
[Definitions][defs] · [Theorems][thms] · [Institution reference][gb]

## Signatures and profiles

A signature `Sig` has carriers `ThreadId`, `CoreId` and `Event`. A morphism
`f : A ⟶ B` maps these carriers into the corresponding carriers of `B`.
Thread maps are injective so that threads that act independently stay distinct
and an event owner outside a synchronization's participant list stays outside
the renamed list. Core and payload maps are ordinary functions and may identify
labels. The category uses componentwise identity and composition. State and
scheduler `Choice` belong to the operational interpretation, which quantifies
over decisions and final states.

| Observation functor | What a candidate observation records |
| --- | --- |
| `namedWords` | A chronological word of thread-owned events and synchronization participant lists. |
| `concurrentTraces` | The class of such a word modulo the existing thread-independence swaps. Its renaming is `ConcurrentTrace.mapTrace`. |
| `coreWords` | A chronological word with an emitting core on every letter, including synchronization letters. A core can emit on behalf of different threads at different positions. |

The thread-only profiles ignore the `CoreId` carrier and its map, so `Unit`
suffices there. Core tags are observed on raw words. For example, swapping two
thread-independent events could change the order seen on a shared core.
The construction uses no quotient of core words or core projection from the
thread quotient. `classic` also accepts any functor `Sig ⥤ Type u` of candidate
observations. [Concurrent traces][traces]

## Sentences, models and reducts

Sentences are finite propositional formulas built from truth, `possible o`,
negation, conjunction and disjunction. An atom tests exact membership of its
word or trace class in the model. A positive atom requires a witness and a
negated atom rules out that candidate. A model is a set of admitted
observations, possibly infinite, with inclusion as the arrows of its model
category. The logic can test any finite collection of fixed candidates.
It has no temporal operators, fairness, termination or quantification over
unbounded traces.

For a signature morphism `f` with observation map `obs(f)`, sentence translation
applies `obs(f)` to every atom. The model reduct is the preimage
`{o | obs(f)(o) ∈ M}`. It acts contravariantly and preserves inclusion.
Membership gives the satisfaction equivalence on each atom. Lean proves the
equivalence for all formulas and the identity and composition laws on both
translations. `classic` packages these data into the sentence and model
functors with the satisfaction condition.

All three profiles have behavioral reducts. For example, if a payload map
identifies two payloads, both source candidates test the same target
observation. Taking a reduct constructs a behavior set and provides no
operational reconstruction of the state, choices or scheduler of a VM.

## VM interpretation and examples

`ofVM` puts an observation in the model when some successful finite schedule
from the given initial state produces a chronological word that the observer
maps to it. The empty schedule contributes the observation of the empty word.
A blocked branch contributes no outcome for the failed schedule. Successful
prefixes still contribute. `namedModel` uses the identity observer and
`concurrentModel` takes the quotient class. For the latter, the schedule
witness executes a representative of the class. `mem_ofVM_iff_run` proves
that the interpretation agrees exactly with observing the union of all
finite lengths of the existing monadic runner. [Multicore VM executions][vm]

The core-word profile has its own behavioral models and signature morphisms.
A VM interpretation with actual core tags needs a source of core-tagged
chronological observations. The current abstract VM emits thread-only words.

The Lean examples rename thread IDs from `Fin 2` to `Nat`, core IDs from
`Bool` to `Nat` and payloads from `Bool` to `Option Bool`. They check the
renamed synchronization participants, a positive and a negative test across
a core-word reduct, and the named and quotient observations of the abstract
VM's register executor. [Lean examples][examples]

## Scoped checks

```sh
make check CHECK_TARGETS='+Silmaril.Machine.MulticoreVM.Institution.Thms +Silmaril.Proofs.Machine.MulticoreVM.Institution.Regression'
```

[defs]: ../../Silmaril/Machine/MulticoreVM/Institution/Defs.lean
[thms]: ../../Silmaril/Machine/MulticoreVM/Institution/Thms.lean
[examples]: ../../Silmaril/Proofs/Machine/MulticoreVM/Institution/Regression.lean
[traces]: concurrent-traces.md
[vm]: multicore-vm.md
[gb]: https://doi.org/10.1145/147508.147524
