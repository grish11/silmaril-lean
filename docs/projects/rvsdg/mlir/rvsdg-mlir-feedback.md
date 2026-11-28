# Scoped MLIR-style lowering for stateless RVSDG feedback

The source is a numbered `NestedTheta.Graph` admitted by the stateless
institution's `NoState` predicate. It can have primitive, γ and θ bindings at
any nesting depth. Primitive interpretations are total over the fixed value
alphabet. A θ may take indefinitely many body activations, so the observable
result is a partial, ordered tuple.

The target is a project-defined, single-block region with explicit SSA
bindings. Group zero is the ordered block argument tuple. Every binding adds
one group of result names, with references to a particular port of an earlier
group. Each nested region opens with only its own argument group. The lowering
reuses the corpus's typed ports, tuples and reference lookup and gives every
source binding a target binding, including bindings with unused results or
empty result profiles.

| Binding | Execution |
| --- | --- |
| Primitive | Evaluate the primitive once on its typed operands and bind its entire result tuple. |
| γ | Use the leading selector to choose a single isolated arm. Pass the remaining tuple as its ordered arguments and bind its yield. |
| θ | Invoke the isolated body on the seed carry. The body yields a two-way selector followed by the updated carry. Selector `1` restarts with that carry, and selector `0` supplies that carry to the continuation. The first activation is mandatory. |

The [acyclic scoped bridge](rvsdg-mlir-graph.md) introduced typed isolated γ
arms and ordered yields for the total fragment. Its expression representation
can omit unused producers. Feedback uses explicit bindings because omitting
an unused θ would discard its execution. The merged [SCF while to CF](https://github.com/hiloopai/silmaril-lean/pull/3167)
and [SCF if with while to CF](https://github.com/hiloopai/silmaril-lean/pull/3198)
use bitvector widths and an `i1` test. The [CF switch and assert fragment](https://github.com/hiloopai/silmaril-lean/pull/3184)
also works over width-indexed operands. This adapter retains the source's
arbitrary value sorts, multi-result primitives and finite multi-way selectors.
It has its own finite-return semantics and requires only merged dependencies.

## Checked observations

`Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.returns_lower_iff` preserves and
reflects finite returns, quantified over every typed input and complete output
tuple. The target computes primitive bindings and γ selection directly. It
specifies θ by reflexive-transitive closure of completed restarts followed by
one completed exit. The proof relates this closure to the source's inductive
`Theta.Iterate` and checks reference lookup and each nested region's scope.
`Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.observe_eq_some_iff` connects the same
relation to the [stateless institution's `Part` observation](../semantics/rvsdg-nested-stateless-institution.md).

The examples check a bypass around a spinning arm, a selected θ that takes
two restarts and exits with a changed heterogeneous carry, and a selected spin
with an explicit infinite path of completed restarts. The parent swaps the
Boolean and natural-number output slots. The spin has a separate proof of no
finite return even when the arm discards all θ results. `Productive` observes
positive restarts of a particular body. Global classification of non-return,
effects, LLVM graph-region semantics and upstream SCF equivalence fall outside
this proof scope.

[Definitions](../../../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Defs.lean) ·
[Theorems](../../../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Thms.lean) ·
[Examples](../../../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Examples.lean) ·
[RVSDG references](../overview.md)

## Checked numbered PEG loops

The [whole-region θ adapter][whole-theta] takes the actual numbered body over
a stateless signature. It wraps the body's primitive labels in the empty-effect
dialect, uses the existing θ embedding, and derives `NoState` from the
data-only entry ports, primitive profiles, and typed wiring. The embedding
keeps the body's port ordering, numbered references, and isolated γ arms.

The [checked PEG adapter][peg-scoped] applies this construction to
`Bundle.compile` from the [ordered PEG θ compiler][peg-theta]. It reuses the
bundle's guard and simultaneous update schedules. Its finite-return theorem
compares the generated scoped block with the precise numbered graph in the
existing total PEG model. The SCF corollary compares it with the [native
`scf.while`][peg-scf] produced from the same bundle under the given bitvector profile.
Both observations include the complete carry tuple. The
[fixture][scoped-fixture] executes the emitted scoped block through two restarts
and a stopping activation, and checks SCF agreement for immediate exit and
16-bit overflow.

## Ordered CF for a recovered mixed θ

The classifier consumes and returns a live runtime token. The mixed prefix
also carries that token across its
carrier conversion and recursive suffix. These profiles fail the stateless
bridge's `NoState` predicate. Native `SCF.While` takes a total primitive
evaluator. Its result can express finite fuel exhaustion, while its primitive
contract has no live store or undefined primitive action.
[Singleton recovery][mixed-theta] · [Mixed prefix][mixed-prefix] · [Native SCF][native-scf]

The ordered CF bridge takes the recovery fibre that certifies exact re-emission
of the single numbered θ from #4109. The existing ordered CF contract runs
its blocks in a shared monad. The target has a typed entry branch,
a conditional backedge, and a return. Its project-defined bodies retain both
recovered binding orders and read the old carry in each binding. They evaluate
the bottom-effect value row separately from the classifier. The classifier
runs in `StateT σ Part`, and the scheduler passes its returned store to the
next block on either edge. The body sends only the classifier's restart bit
and the updated value through CF operands. The live token is the scheduler's
input and output store.
[Bridge theorems][mixed-cf] · [Ordered CF contract][cf-ordered] · [#3734][cf-ordered-pr]

The boundary admits one carried value with an explicit isomorphism to a
`BitVec` of positive width. `MixedTheta.returns_iff` preserves and reflects
finite return of the generated ordered CFG at the encoded carry and exact
final store. Fuel exhaustion is separate from an undefined classifier.
The regression recovers both row orders, exercises two backedges and a
stopping activation with a changed store, and proves no finite return after
one restart reaches an undefined classifier. [Regression][mixed-fixture]

This is a Lean integration with project-defined ordered CF bodies and
standard typed CF terminators. Its proof applies to the recovered singleton θ
and finite returns. Native SCF emission, the recursive mixed suffix, general
effects, and infinite traces are outside the admitted interface.

### Ordered CF continuation

The splice recovers the whole numbered prefix from [#4277][mixed-prefix].
Its admitted continuation is one canonical loop leaf with an ordinary
instruction between the header and join classifiers. All carried and exit
values share one word sort. The recovered mixed θ from [#4402][mixed-cf-pr]
now branches to the continuation with its completed payload. The shared
ordered CF scheduler forwards the exact returned store. The continuation
emits its own typed instruction calls and branches, and an `i1` return tag
distinguishes its two exit labels.

`Prefix.returns_iff` preserves and reflects finite return with the exact
exit label, value and store. `Prefix.no_return_iff` covers every output packet
and fuel budget. In the regression, the θ changes store 2 to 2777 and
passes word 3 to the suffix. The suffix reads that store to select its
body, which also uses the store to compute the returned word 222. The
second exit returns store 2783. In the undefined case the suffix receives
word 13 and store 2777, and its selected header action has no finite return.
Both fixtures exercise both recovered binding orders. The target is the
project-defined ordered CF interface, with general suffixes and traces
outside this splice. [Splice theorems][mixed-cf-splice] · [Regression][mixed-fixture]

[whole-theta]: ../../../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Theta/Thms.lean
[peg-scoped]: ../../../../Silmaril/SSA/PEG/Bridge/Theta/Region/MLIR/Scoped/Thms.lean
[peg-theta]: https://github.com/hiloopai/silmaril-lean/pull/3993
[peg-scf]: https://github.com/hiloopai/silmaril-lean/pull/4252
[scoped-fixture]: ../../../../tests/ssa/PEGStructuredTheta.lean
[mixed-theta]: https://github.com/hiloopai/silmaril-lean/pull/4109
[mixed-prefix]: https://github.com/hiloopai/silmaril-lean/pull/4277

[mixed-cf]: ../../../../Silmaril/SSA/RVSDG/MLIR/CF/MixedTheta/Thms.lean
[mixed-cf-pr]: https://github.com/hiloopai/silmaril-lean/pull/4402
[mixed-cf-splice]: ../../../../Silmaril/SSA/RVSDG/MLIR/CF/MixedTheta/Prefix/Thms.lean
[cf-ordered]: ../../../../Silmaril/SSA/MLIR/CF/Ordered/Defs.lean
[cf-ordered-pr]: https://github.com/hiloopai/silmaril-lean/pull/3734
[native-scf]: ../../../../Silmaril/SSA/MLIR/SCF/While/Defs.lean
[mixed-fixture]: ../../../../Silmaril/Proofs/SSA/RVSDG/MLIR/CF/MixedTheta/Regression.lean

## Verify

```sh
lake build --wfail +Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Examples PEGStructuredThetaTests
make check CHECK_TARGETS="+Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Examples \
+Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Check.Defs PEGStructuredThetaTests"
```

The following commands check the mixed θ bridge and its recovery and execution fixture.

```sh
lake build --wfail +Silmaril.Proofs.SSA.RVSDG.MLIR.CF.MixedTheta.Regression
make check CHECK_TARGETS="+Silmaril.Proofs.SSA.RVSDG.MLIR.CF.MixedTheta.Regression \
+Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Check.Defs"
```
