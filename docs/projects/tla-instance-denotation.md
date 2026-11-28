# First-order TLA+ INSTANCE denotation

Import `Silmaril.Logic.Temporal.TLA.DataElab.Instances.Defs`. First call
`Resolution.Instances.check registry root externalLevels`. Pass the resulting
`CheckedInstances` value to a selector along with the semantic external
signature, an expansion depth bound, and the selected definition's
`BindingId`. Each selector uses the level certificate paired with the
resolved registry. A `BindingId` is specific to its graph.

Select a nullary source definition, such as `Out == I!Member`. State
selection admits constant and state levels, and action selection admits
action level. `DataElab.Instances.lowerState` and `lowerAction` select the core
fragment. `lowerCollectionState` and `lowerCollectionAction` add the collection
profile for both home bodies and host expressions, including WITH replacements
and actual arguments. Use `CheckedExpr.eval` with a single valuation or
`Collections.CheckedAction.eval` with rigid, source and target valuations.
Both collection evaluators take `CollectionOperations`, including the tagged
adapter. A source definition can call generated members from named and
anonymous instances, including nested frames. [Replay API](../../Silmaril/Logic/Temporal/TLA/DataElab/Instances/Defs.lean) ·
[Instance resolution and level checking](tla-module-instantiation.md) ·
[Endpoint evaluation](tla-data-elab.md#checked-source-and-target-evaluation) ·
[Collection profile](tla-data-elab.md#state-level-collection-expressions)

## Substitution and endpoints

Qualified arguments keep their resolver paths at each segment. Expansion
binds the namespace arguments first and passes the remaining arguments to the
member's home declaration. When the home is another generated member, replay
continues in the enclosing instance's frame.

A WITH replacement is expanded at its recorded host site, or through its
captured host binding for an implicit replacement. Each one reads the incoming
host frame and that namespace's formals. All replacements are expanded before
the new target frame is installed. This matters when the host and instancee
inherit the same declaration ID. Ordinary source bodies and their LOCAL
helpers still resolve references at their original home sites, within the
current instance's frame. Each invocation has its own substitutions, even
when several instances share a home declaration.

Actuals and replacements are expanded terms. A prime on the host call
or in a home definition shifts flexible reads in the substituted operand to
the target endpoint. Rigid assignments and enclosing witness values retain
their scope. Bounds and bodies inside a primed operand use the target. A
prime whose expanded operand reads `@` from an enclosing EXCEPT reports
`primeCrossesOldValue`, including when a WITH replacement introduces the read.
[Lamport, *Specifying Systems*, §17.8](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=352)

Unsupported syntax and expansion exhaustion report source sites. An expanded
term needs a mathematical value interpretation, including the caller's
ID-keyed external primitives. Direct selection of a generated member,
operator-valued WITH, modal substitution, recursion, theorem substitution,
and source proof verification remain outside this profile.

## Verification

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.DataElab.Instances.Examples \
  +Silmaril.Logic.Temporal.TLA.DataElab.Instances.CollectionExamples \
  +Silmaril.Logic.Temporal.TLA.DataElab.Collections.Examples \
  +Silmaril.Logic.Temporal.TLA.Resolution.Instances.Examples \
  +Silmaril.Logic.Temporal.TLA.DataElab.Examples
python3 -I tests/semantics/tla-collection-binders/check.py
scripts/check-layout.sh
```

The parsed fixture expands repeated and nested calls through the production
lowerer. The kernel checks equations for the selected Boolean actions across
arbitrary source and target Boolean valuations. The same nested fixture
selects a state value and an action using a host prime. Further equations
check implicit shared IDs and simultaneous swaps. Guards check argument levels
at each segment, unsupported operator replacements, and the depth bound.
[Core regressions](../../Silmaril/Logic/Temporal/TLA/DataElab/Instances/Examples.lean)

The collection fixture checks equations for a named call with a record actual,
an anonymous call building a graph after a simultaneous swap, and two actions.
One primes the whole named call, including a flexible host read whose name
also occurs as a home binder. The other reads the old graph entry at the
source and a substituted variable at the target. Negative cases check the
state selector, a level ceiling at the WITH site, and a prime that crosses an
enclosing `@` binding. The pinned corpus gate also replays the original
`WriteThroughCache.Coherence` body in a projected module through a parsed
host. [Collection regressions](../../Silmaril/Logic/Temporal/TLA/DataElab/Instances/CollectionExamples.lean) ·
[Corpus gate and scope](tla-data-elab.md#writethroughcache-corpus-gate)
