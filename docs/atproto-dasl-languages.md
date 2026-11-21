# Named DASL languages

## Presentations and satisfaction

[`PartialLanguage`](../Silmaril/Formats/Dasl/Language/Defs.lean) is a predicate
on a root name and a named partial tree. Its `roots` are the names with
witnesses. A witness records the shallow root binding and the known object
and blob targets; an unresolved reference records no target binding. The
abstract [`Stores.collect`](../Silmaril/Semantics/Naming/Observations/Thms.lean)
unions exactly the contributions of the witnesses. `observed_subset_iff`
proves that the result is the least relation satisfying the presentation.
Satisfaction means inclusion. A common binding extension exists exactly when
the union is binding (`Stores.mergeCompatible_iff`); **neither** operand need
already contain the other.

`Saturated` means closed under `Extends` steps whose resulting root and known
targets are already included in the language's observed relation. `expand`
admits only refinements justified by a jointly binding union with an external
relation. It preserves witnesses and shallow named roots and is saturated both
in the union and under its own observations. Each new observation must be in
the union. The expanded presentation satisfies the **external relation alone**
exactly when that relation already included the starting observations.

`realize` takes shallow named roots and a relation and returns all the named
partial witnesses justified by them. If the relation is binding, the result
is binding and saturated. It recovers the advertised shallow roots if each
one is backed by a root binding. In the other direction,
`realize_observed_iff` gives an exact reconstruction test: the original
language must contain a shallow seed at each witnessed root and be saturated
under its own observations. Neither direction recovers arbitrary extra
bindings: `realize_observed_eq_iff` requires every binding of the input
relation to be witnessed. Retain the original relation separately if it can
contain unwitnessed bindings, such as data unreachable from the selected roots.

## Recognizing names and checking queries

`Recognized` lifts a predicate on nameless full DASL values to the names with
a finite full expansion accepted by that predicate. `PartialRecognized` is an
existential positive observation instead. Both are monotone under relation
inclusion, hence under binding extensions. This does not make a particular
policy-selected observation satisfy an arbitrary partial predicate after
refinement. A policy-stable test needs a refinement-monotone predicate (or
another appropriate preservation proof). In neither language does a miss in
an incomplete view prove nonmembership.

[`Queries`](../Silmaril/Semantics/Naming/Query/Defs.lean) is an interface over
abstract object/blob relations, not a concrete CAS map. Successful reads must
belong to the reference relation. Missing and invalid reads make no assertion
about the reference. [`Check.run`](../Silmaril/Formats/Dasl/Language/Check/Thms.lean)
requires no name equality or hash algorithm. It walks inline containers and
charges a unit of fuel per link on each path, not for the root read. It
returns `undecided` with the blocking link and the reason (fuel, missing, or
invalid). Only a certified full expansion reaches the supplied Boolean
predicate. If that predicate reflects a language, acceptance is sound in the
reference and all extensions. Rejection of a full witness is sound in any
binding extension: every full expansion of that name is the same. No negative
answer is inferred solely from a missing read, exhausted budget, or invalid
wire, and no reverse name uniqueness is required.

The [wire adapter](../Silmaril/Formats/Dasl/Language/Check/Wire/Defs.lean) reuses
the canonical DASL reader and preserves malformed object bytes and wrong codec
kinds as invalid. Its decoded graph is binding by determinism, not by hash
injectivity. To check against another reference, supply inclusion of that
graph; hash authentication is a separate obligation.

## Remaining integration

- [ ] **Grammars:** provide a grammar or schema frontend with an interpretation
  into predicates on DASL values and prove that its executable test reflects
  that interpretation. If transporting a word/tree grammar through an
  encoding, state the embedding/retraction and preservation hypotheses;
  this layer makes no universality claim.
- [ ] **Query coverage:** characterize completeness at sufficient fuel for
  readers covering all reachable bindings. To prove negative answers without
  an actual full witness, supply a closed-view or other sound certificate.
  Do not treat the current read failures as such certificates.
- [ ] **WASM and Git:** connect verified host queries or a Git object adapter
  to the reference relation, including decoding, kind checks, object identity
  and trust in read results. No WASM compilation or Git adapter is proved here.
- [ ] **Other milestones:** see the [DASL foundation checklist](atproto-dasl.md#remaining-work)
  for canonical wire roundtrips, partial refinement, encodings and bounds,
  and Prolly/MST operations.

## Checks

```sh
lake build --wfail Silmaril.Formats.Dasl.Language.Check.Wire.Thms
lake env lean -DwarningAsError=true --run tests/formats/DaslLanguage.lean
```
