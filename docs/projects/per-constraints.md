# Partial-equivalence constraints

The `Silmaril.Calculi.PERConstraints` calculus uses the existing `Formats.PER`
interface. A syntax is a carrier with total functions as morphisms. On a fixed
carrier, morphisms between PERs are relatedness-preserving endofunctions. The
total category allows the carrier to vary and forgets to the syntax category.
Morphisms act on all terms, including invalid ones, and are not identified just
because they agree on the PER quotient. The fixed-carrier category is not the
strict fiber of the forgetful functor: its arrows can have nonidentity syntax maps.

## Constraint semantics

| Form | Satisfaction by a PER |
| --- | --- |
| `EQ` on a set or finset | All pairs are related, including the diagonal. A nonempty collection is contained in the class of any chosen member. |
| `DISTINCT` on a set or finset | Every member is valid, and different members are unrelated. |
| `DISTINCTList` | Every occurrence is valid, and different positions are unrelated. Any duplicate makes the constraint unsatisfiable. Permutations preserve satisfaction. |

All three forms accept the empty collection and test validity on a singleton.
`Bound` is the sum of set EQ and list DISTINCT. A finite set DISTINCT can be
included by enumerating it **before** translation; `Bound.holds_ofFinsetDistinct`
justifies that inclusion. `distinct_list_iff_finset` shows what is lost by
forgetting occurrences: the list assertion also requires `Nodup`.

`All` and `Any` quantify over sets; `AllFinset` and `AnyFinset` restrict those
evaluators to finsets. CNF is an AND of ORs, and DNF an OR of ANDs. An empty AND
is true and an empty OR is false, at either level. `holds_ofFinsets` compares
the two-level finite evaluators with the set semantics. `CNF.toDNF` takes the
disjunction of all sets meeting every clause; it preserves satisfaction, SAT and
UNSAT, but is not a finite normalizer.

## Institutions and SAT

The CNF institution translates sentences forward and pulls PERs back along a
syntax function. Its model categories are discrete, **not** the categories of
PER-preserving syntax maps. The institution is a `Syntax ⥤ Room` with an `Inst`
registration in the logic graph (`calculi.per_constraints`). The same institution
restricts to shallow DASL link renamings and to extensional JSON atom replacement
at fixed object keys. JSON replacement uses the existing `Json.bind` laws; these
adapters do not impose a codec, wire profile or congruence on the PER models.

EQ translates by direct image. Occurrence DISTINCT translates by `List.map`,
which retains both positions even when their terms become equal. Set DISTINCT
transports by image only under an injectivity condition on the designated set.
The Boolean examples check both behaviors under a constant map: the imaged
set can become a valid singleton, but the translated list is unsatisfiable.
In particular SAT reflects from translation to source, but does not in general
preserve from source to translation.

A dictionary is a key-to-optional-bound function. Its conjunction compiles to
the CNF of its singleton clauses, preserving model satisfaction and therefore
SAT and UNSAT. SAT means a PER witness exists; UNSAT rules out every PER witness.
The logic graph registers and checks a satisfiable separation dictionary and an
unsatisfiable equality/distinctness conflict. There is no decision procedure or
claim of decidability for the infinitary language.

```sh
make check CHECK_TARGETS='Silmaril.Calculi.PERConstraints.Syntax.Formats.Thms Silmaril.LogicGraph.Nodes.Calculi.PERConstraints.Defs'
```

## Finite presentations and normalization

`Finite.Thms` extends the interface without changing the institution or its
models. Set and finset EQ/DISTINCT use membership; an EQ over a list or multiset
is equivalent to EQ over its deduplicated finset. For list and multiset DISTINCT,
this comparison additionally requires `Nodup`. The multiset is a quotient by
list permutation, **not** by duplicate elimination, and its `map` preserves
occurrences. Every atomic form is vacuous on empty input and checks validity on
a singleton; a repeated occurrence is unsatisfiable for DISTINCT even if the
repeated term itself is invalid.

At Boolean AND/OR nodes, order and multiplicity never affect satisfaction.
List and multiset evaluators agree with their deduplicated finset evaluators.
`CNF.ofAnd` makes singleton clauses and `CNF.ofOr` makes one clause; both commute
with syntax translation. Nested finsets, lists and multisets also embed in the
set-based CNF and DNF semantics. The infinitary `DNF.toCNF` is the dual of
`CNF.toDNF` and preserves satisfaction.

For a finite list of rows, `choices` concretely enumerates one occurrence per
row. Reading each result as a disjunction converts DNF to CNF; reading each as a
conjunction converts CNF to DNF. The correctness theorem for finite DNF applies
in the original institution, including along non-injective syntax maps. The
number of output rows, before any deduplication, is exactly the product of input
row lengths: `2^n` for `n` binary rows. No optimization, model evaluation or SAT
solver is supplied; the finite algorithm transforms only the Boolean skeleton.

```sh
make check CHECK_TARGETS='Silmaril.Calculi.PERConstraints.Finite.Examples.Thms'
```

## Intervals and admissible completions

`Interval.Thms` adds C3 semantics over the existing `CNF` and `PER` types. An
ordered pair `[L, U]` denotes every PER `M` with `L ≤ M ≤ U`, where `≤` is
relation inclusion. An admissibility predicate can impose guarded constructor
closure or a background theory. `Bounds.Certain` quantifies over every admissible
completion, `Bounds.Refuted` asks whether each completion refutes the query, and
`Bounds.Possible` asks for a satisfying completion. Both universal flags hold on
an empty fiber, as in `conflict_fiber_empty` for the original conflicting
EQ/DISTINCT dictionary. `Bounds.satisfaction_exact` and
`Bounds.reduct_exact` recover the original institution's satisfaction and reduct
on singleton intervals.

`CNF.holds_mono_of_eqOnly` covers arbitrary conjunctions and disjunctions of EQ
atoms. `Bounds.eqOnly_endpoints` tests certainty at `L` and possibility at `U`
when both endpoints are admissible. With occurrence DISTINCT, increasing a PER
can add required validity or destroy required separation. If all designated terms
are already valid at `L`, `Bounds.distinctList_endpoints` gives the reversed tests
for that atom. Without that domain hypothesis, `distinct_interior_only` shows
that both endpoints can reject a CNF satisfied by an interior PER.

A minimal or maximal model rules out a strictly smaller or larger admissible
model, respectively. A least or greatest model must compare with every
admissible model. `either_pair_two_minimal` and `either_pair_no_least` exhibit
this difference for `a = b ∨ b = c`. `separate_ends_two_maximal` and
`separate_ends_no_greatest` exhibit it for `DISTINCT [a, c]`. Joining the two
maximal witnesses would identify `a` and `c` by transitivity. These examples
preclude a single interval description of the respective model families.
For a conjunction of EQs with a closed, satisfying upper bound,
`eq_conjunction_isLeast` constructs a least completion by applying the existing
[guarded congruence closure](per-constraint-congruence.md) to the lower bound
joined with the required pairs. The upper bound itself is then greatest.

`Bounds.pull_mapsTo` pulls back both endpoints and every completion whose
admissibility transports. `Bounds.pull_mapsTo_closed` applies this to guarded
signature morphisms. `Bounds.flags_of_subset` preserves both universal flags as
the completion family shrinks. `Bounds.flags_map` compares the reduct's evidence
to the target translation's evidence in that direction, component by component.
When every admissible source completion lifts, `Bounds.flags_map_iff_of_coverage`
gives both flag equivalences and `Bounds.completion_image_eq_of_coverage`
identifies the reduct image with the source family. `Bounds.pull_surjOn_of_injective`
proves coverage for unrestricted PERs along injective term maps. For a collapsing
map, `collapse_refutation_strict` shows that the refutation flag can increase, and
`collapse_reduct_not_least` shows that reduct can lose leastness in a theory
fiber. A generalized institution adapter can evaluate the same completion sets
with its evidence type. An adapter for restricted fibers also needs to choose
admissibility coherently across its signatures.

```sh
make check CHECK_TARGETS='+Silmaril.Calculi.PERConstraints.Interval.Examples.Thms'
```
