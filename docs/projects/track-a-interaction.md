# Track A interaction and refinement

Import the headers under `Silmaril.Semantics.TrackA.Interaction`.

| Header | Interface |
| --- | --- |
| `Thms` | Dependent signatures, request translation, delayed coalgebras, finite and infinite observations, stateful handling, and guarded feedback |
| `WeakITree.Thms` | Adapter from `Silmaril.Elgot.ITree.Tree` |
| `Guarded.Thms` | Context-indexed first-order interaction and its dependent-sum erasure |
| `UB.Thms` | Explicit UB, catastrophic closure, bottom extension, and trace transformer composition |

## Interaction and observations

A signature gives a response type for each request. A morphism maps requests
forward and decodes the new response for the old continuation. `Node.relabel`
preserves identity and composition. An exchange is a dependent pair of a
request and the response it received. Mapping completed exchanges forward
would need additional data on responses.

A coalgebra gives one layer per state. A forest supplies a family of roots in
one coalgebra, and a tree has one root. `ITree` has returns, tau, and visible
requests. `CTree` adds finite choices, including arity zero. The general
`ChoiceTree` permits a dependent family of choice arities. The two choice
kinds have distinct raw edge labels. The weak policy hides both kinds and
counts both as internal progress. This is the may-trace policy of this
development. The CTree paper develops two separate kinds of branch with a
different induced LTS and studies bisimulation. The ITree constructors and
the distinction between choice kinds are based on the cited ITree and CTree
presentations. [Interaction Trees](https://doi.org/10.1145/3371119)
[Choice Trees](https://doi.org/10.1145/3571254)

The finite observations end in a return, a request with no possible reply,
a choice of arity zero, or silent divergence. Divergence requires an infinite
path of actual internal edges after the last exchange. An infinite exchange
observation requires a single path with a finite internal segment before
each successive exchange. The checked countdown example offers a completed
run with every finite number of repetitions and rules out the infinite
repetition. A forest with no roots has empty observations. Refinement is
inclusion from implementation to specification, and observational equivalence
is mutual inclusion. A leading tau preserves both kinds of observation.
[Definitions](../../Silmaril/Semantics/TrackA/Interaction/Defs.lean)
[Theorems](../../Silmaril/Semantics/TrackA/Interaction/Thms.lean)
[Regression](../../Silmaril/Proofs/Semantics/TrackA/Interaction/Regression.lean)

`Guarded.GITree` covers a first-order fragment with context-dependent
effects. Each context has its own signature, and each reply determines the
continuation's context. The erasure stores the context in the state and the
exchange. `Guarded.Forest.step_vis` checks its visible-step equation.
Higher-order effects, a guarded-recursive domain model, and the associated
program logic remain follow-ups.
[Guarded header](../../Silmaril/Semantics/TrackA/Interaction/Guarded/Thms.lean)
[Modular Denotational Semantics for Effects with Guarded Interaction Trees](https://doi.org/10.1145/3632854)
[Context-Dependent Effects and Concurrency in Guarded Interaction Trees](https://doi.org/10.1145/3861008)

`WeakITree.toDelayed` reuses the landed weak tree destructor. It preserves
return and visible layers, and the weak divergence case becomes an actual
silent self-loop. Finite tau structure was already erased in the source.
`Coalgebra.handle` performs one total stateful request handler atomically
and hides the exchange behind tau. `Coalgebra.iterate` restarts from a
recursive return with one tau. The checked laws cover the handled request
equation and silent feedback self-loops. The existing weak ITree library
provides complete-Elgot iteration and an interpretation interface under its
stated hypotheses. The delayed and choice models here have no finality,
weak bisimulation, handler adequacy, or general Elgot-law theorem.
[Weak adapter](../../Silmaril/Semantics/TrackA/Interaction/WeakITree/Thms.lean)
[Existing iteration](../../Silmaril/Semantics/ITree/Thms.lean)
[Existing interpretation](../../Silmaril/Semantics/ITreeInterpret/Thms.lean)

## Undefined behavior at a trace boundary

`Explicit T` is the inclusion lattice on sets of `Option T`. Its extra
`none` is explicit UB. A tree using `Option A` returns this marker as a
terminal result, keeping the preceding exchanges in the tree trace.
`UB.atBoundary` collects complete traces for whole-row catastrophe. This
projection forgets the prefix of a UB run and retains ordinary errors,
stuckness, deadlock, divergence, and infinite exchange traces. This closure
applies to the whole row of a trace transformer. Prefix-preserving
catastrophe is a different contract, already exemplified by the container
behavior model.
[UB definitions](../../Silmaril/Semantics/TrackA/Interaction/UB/Defs.lean)
[Container closure](../../Silmaril/Containers/Behaviour/Defs.lean)

The catastrophic complete lattice is the fixed-point order of saturation.
Collapse is left adjoint to the inclusion of saturated sets and preserves
all joins. It is exact on UB-free sets. The comparison
`collapse s ≤ collapse t` holds exactly when `t` contains UB or `s ⊆ t`.
A binary meet commutes with collapse when the UB marker agrees on its two
operands. The UB singleton and any ordinary singleton witness failure
without that premise. The bottom is the empty set and the top is the unique
closed set containing UB. In particular, even the set of all ordinary
behaviors can be UB-free.

The nonempty fragment is closed under nonempty joins. With two distinct
ordinary traces their singletons have no common lower bound in the fragment.
For an inhabited subsingleton trace type, the ordinary singleton is least.
Adjoining a bottom recovers the catastrophic complete lattice by order
isomorphism. A trace transformer has one nonempty set of ordinary outputs
or UB per input trace. Sequential composition is monotone, associative,
and unital. A composite row is UB exactly when its first row is UB or a
reachable trace selects a continuation row with UB.
[UB theorems](../../Silmaril/Semantics/TrackA/Interaction/UB/Thms.lean)

## Integration boundary

The SQLite VFS already exposes `Request`, `Response`, `Exchange` and a
stateful `Handler`. Its request family fits `Signature`, and its handler
has the shape required by `Coalgebra.Handler`. The container adapter splits
requests and replies into distinct events. Relating those events to the
completed exchanges here, including which open requests count as blocked,
requires a separate theorem. The proposed institution can use
`Signature.Hom` and the refinement order directly and must supply its own
signature-change semantics and satisfaction condition.
[SQLite VFS](../../Silmaril/Machine/SqliteVfs/Defs.lean)
[Container VFS adapter](../../Silmaril/Containers/SqliteVfs/Defs.lean)

## Checks

```sh
lake build --wfail +Silmaril.Proofs.Semantics.TrackA.Interaction.Regression
make check CHECK_TARGETS=+Silmaril.Proofs.Semantics.TrackA.Interaction.Regression
```

The regression imports all theorem headers and exercises the infinite
observation distinction, empty forests, separate terminal outcomes, and
nonempty lattice examples. The modules belong to the existing Semantics
region and Lake globs.
