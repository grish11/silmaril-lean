# Partial sequences and concurrent trace ideals

Import [`Silmaril.Semantics.ConcurrentTrace.Ideals.Thms`][ideals].
The development is parameterized by the finite word interpretation. For a
Mazurkiewicz trace monoid, use its finite word quotient as the interpretation
and order finite classes by left divisibility, so `x ≤ y` means
`y = x * z` for some finite class `z`. A word extension gives exactly this
factorization. The [event/sync instance][event-sync] uses these public
interfaces to connect finite classes and ideal-prefix observations.
[The Book of Traces][book-of-traces] gives the
standard finite trace-monoid terminology.

## Observations and equality

- [`PartialSequence`][sequences] has finite pending and completed words
  and infinite streams. The raw observation consists of the finite list
  prefixes in their original order and the optional result.
  [`prefixEquiv`][prefixes] identifies these sequences with coherent bounded
  list cuts, including the condition that a result requires a finite cut.
  `eq_iff_observations` gives the equivalent criterion using membership in
  the set of raw prefixes and equality of optional results. A pending finite
  word records available observations. The constructor alone cannot tell
  whether the source computation stopped, blocked, or silently diverged.
- [`prefixIdeal`][ideals] takes the downward closure of the finite quotient
  classes of the cuts of one sequence. `Ideals.Trace.ofSequence_eq_iff` compares two
  presentations by mutual cofinal domination of the classes and equality of
  optional results. In the commuting two-letter alphabet, the streams
  `abbbb…` and `babbb…` have different first quotient prefixes and equal
  ideals. The [regression][regression] checks both facts. Finite swaps can
  change the raw cuts that witness membership in a quotient ideal.
- Each represented ideal has a countable cofinal chain. The ambient ideal
  type also contains the ideal of all finite subsets of an uncountable
  alphabet. The regression proves that no sequence with finite-subset
  observations represents that ideal. Each cut contributes only finitely
  many elements, and the countable union of its cuts cannot cover the alphabet.
- A finite word generates the principal ideal of its class.
  `Ideals.Trace.ofFinite_injective` embeds finite word classes with their optional
  result when the finite order is antisymmetric. A monotone length function
  recovering raw word length rules out principal ideals for infinite streams.
  Erasing interpretations can lose this distinction for pending words.
- `Ideals.Trace.observe_map` gives the naturality square. A relabelling that commutes
  with the finite word maps acts on ideals by downward closure of their image
  under the monotone map of finite classes. A result map acts on the optional
  result.

## Iteration and integration

[Infinite paths][paths] require actual transitions in a relation.
[Weak interaction trees][itrees] use coherent observations of visible events,
and their [finite traces][itree-traces] retain replies, pending requests,
and returns. Their empty visible prefix is also observable under silent
divergence. [PartialWriter][writer] accumulates deterministic log observations
by a supremum using its ordered log algebra. [CALCO printing][printing] has
explicit infinite observations and uses a greatest solution for productive
loops. [Finite Brookes behaviors][brookes] use a least solution on completed
traces and give empty completed behavior for a loop with no exit. These
interfaces make different observations about an endlessly emitting loop.

The [regression][regression] checks the mismatch directly. For sets of whole
traces ordered by inclusion, prefixing one event maps the empty set to itself.
Its least solution is empty even though the singleton containing the constant
infinite stream is another fixed point. On finite prefix lengths, the same
loop unfolds by adding the empty prefix and extending old prefixes by one
event. Its least solution contains every length. Substituting ideals for
whole traces inside the same powerset construction still leaves the empty set
at bottom and does not by itself accumulate prefix observations.

A divergence-observing nondeterministic model needs a choice of observation
order and bottom, a rule for accumulating prefix observations that survives
an always-recursive branch, and a policy for reconstructing individual
infinite behaviors if those are observable. A union of alternatives can
contain incompatible prefixes and need not be an ideal of one execution. In particular, the ambient ideal order
need not be the complete lattice required by `ContinuousLog`.
Bind must preserve the chosen observations when a result never arrives, and
compose the finite interpretations when it does.

The [Kleene fusion theorem][fusion] supplies a reusable part of the least
solution argument. On pointed omega-complete partial orders, a strict
omega-continuous map that intertwines the continuous unfoldings transports
their chosen least fixed points. For a proposed lawful monad with these
orders on computations, continuity of bind in its continuation gives
continuous unfoldings. Naturality uses strict, continuous postcomposition
with a Kleisli arrow. Pure uniformity uses strict, continuous precomposition
with a state map. Each application requires the corresponding unfolding
square, and codiagonal still requires a nested least-solution argument.
Only after proving the monadic equations and these laws can the
[CALCO total-guard adapter][complete-elgot] export the result as complete Elgot
iteration. This development provides the observation and quotient layer and
the fusion result.

## Reproduce

```sh
lake build --wfail +Silmaril.Semantics.ConcurrentTrace.Ideals.Thms \
  +Silmaril.Semantics.Domain.Kleene.Fusion.Thms \
  +Silmaril.Proofs.Semantics.ConcurrentTrace.Ideals.Regression
```

[sequences]: ../../Silmaril/Semantics/ConcurrentTrace/PartialSequence/Defs.lean
[prefixes]: ../../Silmaril/Semantics/ConcurrentTrace/PartialSequence/Thms.lean
[ideals]: ../../Silmaril/Semantics/ConcurrentTrace/Ideals/Thms.lean
[event-sync]: ../../Silmaril/Semantics/ConcurrentTrace/EventSync/Thms.lean
[regression]: ../../Silmaril/Proofs/Semantics/ConcurrentTrace/Ideals/Regression.lean
[paths]: ../../Silmaril/Foundations/InfiniteTrace.lean
[itrees]: ../../Silmaril/Semantics/ITree/Defs.lean
[itree-traces]: ../../Silmaril/Semantics/ITree/Trace/Defs.lean
[writer]: ../../Silmaril/Semantics/TraceModels/Defs.lean
[printing]: calco2019-examples-traces.md
[brookes]: ../../Silmaril/Semantics/Brookes/Iteration/Thms.lean
[fusion]: ../../Silmaril/Semantics/Domain/Kleene/Fusion/Thms.lean
[complete-elgot]: ../../Silmaril/Semantics/Calco2019/CompleteElgot/Thms.lean
[book-of-traces]: https://doi.org/10.1142/2563
