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

The abstract VM emits thread-only words. For a VM with physical core tags,
use the chronological profiles from the placement adapter below.

The Lean examples rename thread IDs from `Fin 2` to `Nat`, core IDs from
`Bool` to `Nat` and payloads from `Bool` to `Option Bool`. They check the
renamed synchronization participants, a positive and a negative test across
a core-word reduct, and the named and quotient observations of the abstract
VM's register executor. [Lean examples][examples]

## Natural observation projections

Import `Silmaril.Machine.MulticoreVM.Institution.Projection.Thms` to use a
natural family `π : F ⟶ G` of projections between observation functors
`F G : Sig ⥤ Type u`. For every signature map `f : A ⟶ B`, naturality gives
`π_B (F(f)(x)) = G(f)(π_A(x))`. [Projection API][projection]

`roomProjection π` maps this square into rooms using the existing institution
functor. Its components inherit the satisfaction condition, and
`roomProjection_id` and `roomProjection_comp` give its categorical laws.
`sentence_natural` proves that the two forward translations agree on every
formula. `reduct_natural` proves that the two backward paths of inverse-image
reducts agree. `image_natural` proves the two forward paths of direct images
agree on behavior sets. `image_ofVM` and `ofVM_natural` apply the direct-image
laws to observations of the same actual VM schedules. For example,
`namedToConcurrent` makes `concurrentModel` the direct image of `namedModel`.

For a rich behavior set `M` in the target signature, the mixed square has one
general inclusion, written below with `fF := F.map f` and `fG := G.map f`.

```text
π_A '' (fF ⁻¹' M) ⊆ fG ⁻¹' (π_B '' M)
```

`image_reduct_eq_iff` proves equality for every `M` exactly when the square
has the weak pullback witness property. For any visible source observation
`a` and rich target observation `b` with `π_B b = fG a`, there must be a rich
source observation `x` with `π_A x = a` and `fF x = b`. The regression shows
strict inclusion when a visible word has a target witness on a core outside
the core renaming's image. [Projection regressions][projection-tests]

## Physical core placement

Import `Silmaril.Machine.MulticoreVM.Institution.Placed.Thms` for the adapter
to the placed machine. `placedWords` retains the executing core and thread of
each letter, including the sync actor and participant list. `coreLocalWords`
is the chronological core projection with `none` for syncs and `some` for
payloads. Use `classic placedWords` or `classic coreLocalWords` to instantiate
the same institution. [Placed API][placed]

`ofPlaced instruction initial` gives the full behavior set. Take the direct
image along `placedToNamed.app A` for the chronological thread behavior or
`placedToCore.app A` for the chronological core behavior. The thread quotient
is available through `placedToNamed ≫ namedToConcurrent`. The core view uses
the original chronological word because a thread-independent swap need not
preserve the order seen on a core. `placed_named_subset` proves the named
projection is included in the abstract VM's behavior when the instruction
satisfies `Placed.Instruction.Refines`. That simulation supplies inclusion
from actual placed runs. Equality with the abstract behavior would also
require execution witnesses in the other direction.

## Atomic, critical-region and yield-only models

Import `Silmaril.Machine.MulticoreVM.Institution.Schedulers.Thms`.
`Scheduler.atomic`, `Scheduler.critical` and `Scheduler.cooperative` use
their existing finite schedule relations. The programs supply the
instruction and state carriers, including any local, program or shared
state. The cooperative adapter also takes a dispatch policy. Programs with
a separate internal effect type can use `interpretEffects` to interpret
each raw effect as a fragment of the signature's event language.
[Scheduler API][schedulers] · [Critical-region semantics][critical]

In `classic scheduledWords`, a candidate is the chronological list of
thread IDs and move kinds paired with the chronological effect word. Move
kinds distinguish ordinary instructions, enter, leave, dispatch, yield and
retirement. An ordinary instruction still contributes a decision when its
effect fragment is empty. `classic countedWords` retains the ordinary
instruction count and the same effect word. Both profiles use successful
finite prefixes and hide final states and instruction operands. The
operational refinement theorems retain those endpoints and the full erased
schedule. `Scheduler.namedModel_eq` recovers the original named model
by keeping just the effect word.

For `f : A ⟶ B`, the original signature homomorphism renames thread
IDs injectively and maps events and core labels by functions. These profiles
use the thread and event maps, including the participant lists of
synchronization letters. `scheduledToCounted` and `countedToNamed` are
natural projections. `Scheduler.satisfaction_renaming` and
`Scheduler.satisfaction_counted_renaming` specialize the institution's
sentence translation and inverse-image reduct to actual scheduler models.
Reduct tests each candidate by translating it into the target signature.
For example, a schedule atom translated along erasure tests the counted
observation, allowing any schedule witness with that count and word.

A forward operational interpretation requires a separate witness:

- `StepMap` maps states and instructions and preserves the atomic relation
  with the renamed effect fragment. `StepMap.ofEffects` also maps raw effects,
  with preservation of the raw transition and commutation with its observer.
- `CriticalMap` preserves both control continuations and reflects completion
  on mapped threads for the activity guard. It maps the optional owner by
  the thread embedding, preserving the dispatcher's free and owner cases.
- `CooperativeMap` preserves yield continuations and allowed dispatch
  decisions. Its finished predicate must agree on mapped threads, since
  retirement needs completion and ordinary steps need activity. Runnable
  witnesses then map by the ordinary and yield transition laws.

`StepMap.scheduled` maps a run to a target run from the mapped initial state
with the mapped endpoint. `CriticalMap.atomicSchedule_map` and
`CooperativeMap.atomicSchedule_map` commute with erasure of control
decisions. At the model level, `Scheduler.countedImage_natural` identifies
the two paths that rename and erase the same source executions, and
`Scheduler.Forward.countedModel_image_subset` puts that common image inside
the target's actual behavior. Equality with the full target model requires
witnesses lifting its observations to executions of the source. The logical
reduct still exists for every signature map. It does not supply such lifts.

`Scheduler.critical_counted_subset` and
`Scheduler.cooperative_counted_subset` give refinement into the same atomic
model. `Scheduler.countedModel_regionFree` and
`Scheduler.countedModel_everyAtomic` give equalities for the region-free and
every-atomic-yield boundary modes respectively. The counted comparison
makes no equality claim about the richer schedule logs.

The regressions check a silent atomic step inside a region, a foreign step
enabled by the program but excluded by ownership, and the actual switch
after leave. The second interpretation changes thread names from `Bool` to
`Nat`, adds a mode to the state, maps instructions into an option type,
and changes optional raw effects into lists of reports. It checks forward
execution and satisfaction of a renamed schedule test.
[Lean regressions][scheduler-tests]

## Scoped checks

```sh
make check CHECK_TARGETS='+Silmaril.Machine.MulticoreVM.Institution.Thms +Silmaril.Proofs.Machine.MulticoreVM.Institution.Regression +Silmaril.Proofs.Machine.MulticoreVM.Institution.ProjectionRegression'
make check CHECK_TARGETS='+Silmaril.Machine.MulticoreVM.Institution.Schedulers.Thms +Silmaril.Proofs.Machine.MulticoreVM.Institution.Schedulers.Regression'
```

[defs]: ../../Silmaril/Machine/MulticoreVM/Institution/Defs.lean
[thms]: ../../Silmaril/Machine/MulticoreVM/Institution/Thms.lean
[examples]: ../../Silmaril/Proofs/Machine/MulticoreVM/Institution/Regression.lean
[traces]: concurrent-traces.md
[vm]: multicore-vm.md
[gb]: https://doi.org/10.1145/147508.147524
[projection]: ../../Silmaril/Machine/MulticoreVM/Institution/Projection/Thms.lean
[projection-tests]: ../../Silmaril/Proofs/Machine/MulticoreVM/Institution/ProjectionRegression.lean
[placed]: ../../Silmaril/Machine/MulticoreVM/Institution/Placed/Thms.lean
[schedulers]: ../../Silmaril/Machine/MulticoreVM/Institution/Schedulers/Thms.lean
[critical]: multicore-vm.md#flat-critical-regions
[scheduler-tests]: ../../Silmaril/Proofs/Machine/MulticoreVM/Institution/Schedulers/Regression.lean
