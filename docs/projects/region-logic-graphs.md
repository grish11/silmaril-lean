# Region logic, graph observations, exit queries and effects

Region judgments are primitive relations. Graphs, executions, certificates,
connectives and effect summaries add different observations to those relations.
None changes the [fixed-positive-rule complete lattice](region-lattices.md).
The [region guide](region-extraction.md) describes first-exit semantics and
binary adapters; the [tree guide](region-trees.md) separates dominance children
from outgoing edges. This document explains the additional abstract APIs.

## Truth under renaming and truth under refinement

An institution's satisfaction condition is an **iff**, already at atoms:

```
M ⊨ sentenceMap f p  ↔  reduct f M ⊨ p
```

It compares an observation with the same observation under renamed symbols.
For raw predicates the reduct is precomposition. It does not say that every
truth-preserving simulation reflects truth. For example, replacing the valuation
`False` by `True` preserves all positive atomic truth, but fails to preserve its
negative literal. `Fragments.positive_not_signed` proves this example.

`Logic.Fragments` keeps the atom carrier independent of syntax:

| Fragment | Forms | Empty form |
| --- | --- | --- |
| `base` | one base atom | none |
| `conjunctions` | list of atoms | true |
| `disjunctions` | list of atoms | false |
| `positive` | atoms, truth, falsehood, binary conjunction/disjunction | explicit constants |
| `conjunctionNegation` | atoms, truth, binary conjunction/negation | truth |
| `signedConjunctions` | list of positive/negative base literals | true |

`Translation` requires both naturality under atomic renaming and satisfaction
iff. Atom, conjunction-list and disjunction-list embeddings target `positive`;
`positiveNegation` uses classical De Morgan disjunction; `signedNegation` embeds
a conjunction of signed literals. Translations compose. The list/renaming
proofs and signed-literal translation do not require excluded middle. The
translation of arbitrary positive disjunction into conjunction/negation is
classical: intuitionistically, `¬(¬p ∧ ¬q)` need not imply `p ∨ q`.

`Fragment.rooms` is a proved endofunctor of rooms; composition with a base
institution lifts its syntax without changing its model category or reducts.
`atomicInstitution` supplies an atom-only predicate institution for an arbitrary
`AtomicSignature.Atom`. That type can be the existing abstract
`SegmentAtom Img Assum Seg Support Lab Exits` or `LabelAtom Img Assum Lab Exits`;
it needs no support/exits operations. `Fragment.atomic` adds a chosen fragment.
The existing combined `Logic.Region.Sentence` API remains compatible.

For one-way simulations, `Preserves observed P Q` quantifies over the observed
atoms. `signed_preservation_iff` proves (classically) that preserving both signs
is equivalent to preservation **and reflection** there. It strictly reduces
the allowed positive simulations in the counterexample. It causes no reduction
when reflection was already required (`no_reduction`), including atomic
renamings with institution satisfaction iff. Unobserved atoms are unconstrained.
The graph institutions below use discrete model categories: adding a fragment
does not secretly turn those arrows into an order of model refinements.

## What a graph view retains

`Semantics.Graph.RelGraph V` is a relation on a supplied vertex carrier. An edge
points from source to successor. It permits genuine loops, forgets edge identity,
and has no implicit presence predicate. `GraphLike` supplies this observation;
`CFGLike` additionally supplies entry, internal vertices and declared exits.
An edge does not assert reachability, execution or dominance. To compare only
present vertices, use a chosen subtype or the separate presence model.

| Representation | Direction / multiplicity | Additional data | Loss or obligation |
| --- | --- | --- | --- |
| `RelGraph` | directed; genuine loops; parallel identities forgotten | relation on all supplied vertices | no vertex-presence observation |
| `PresentModel` | same relation | independent present-node set | `WellFormed` optionally requires both edge endpoints present |
| `Incidence.Model` | directed multigraph with edge identities | present-node/edge sets; optional source/target in the signature | unknown endpoint is not absence; `Complete` excludes unknown endpoints on present edges |
| `TotalSignature.toOptional` | directed multigraph | total endpoints injected by `some` | every model is complete |
| `markPresence` | relational, diagonal means presence | off-diagonal real edges | destroys genuine loops; not natural for arbitrary vertex identification |
| `RelGraph.undirected` | undirected simple | symmetrized adjacency | drops orientation, loops and edge identities |

`Logic.Graph.institution` has node signatures, edge-pair sentences, relational
models and inverse-image reducts. `presenceInstitution` has separate node and
edge sentences. Both prove functor laws and satisfaction iff for arbitrary node
maps. Well-formed presence models are closed under reduct.

`Logic.Graph.Incidence.institution` has node/edge signatures with optional
incidence; signature morphisms commute with both endpoint maps, including
unknownness. Its sentences observe node/edge presence and whether an endpoint
is known. It proves satisfaction iff, functor laws, and preservation of
well-formedness and completeness under reduct. Endpoint-equality sentences are
not included: arbitrary vertex identification does not reflect them.

`Model.relation` forgets edge identities and incomplete edges. Its reduct
always preserves a source edge forward (`relation_forward`). Exact agreement
with relational reduct is proved when the node map is injective and the edge
map surjective (`relation_iff`). Surjectivity supplies a missing edge witness;
injectivity reflects its known endpoints. No general equivalence of the
multigraph and relational institutions is claimed.

The checked examples in `Logic.Graph.Examples.Thms` exhibit lost real loops,
failure of marker naturality for a noninjective map, different parallel-edge
sets with equal relational projection, and an incomplete edge indistinguishable
from no edge after projection. They also give a graph isomorphism across `Bool`
and `Fin 2`, the induced minor witness, and a structured iteration's backedge.
These are deterministic abstract examples, not measured binary-corpus coverage.

`Iso` is a vertex equivalence with edge iff, preserving loops and all cross
edges. It has identity, inverse and composition. `Minor` uses **undirected simple
branch sets**, even for a directed input: nonempty disjoint connected vertex
sets, with every source adjacency witnessed between its branch sets. Reflexive
and isomorphism-induced witnesses are proved. A directed-minor theorem or
minor-transitivity theorem is not supplied.

`Structured` chooses a two-boundary grammar: an edge, sequence with a connector,
selection with fresh branching/join vertices, and iteration with a header,
exit and backedge. `WellFormed` requires distinct boundaries and disjoint/fresh
child vertices. `HasStructuredWitness` requires an actual isomorphism to a
well-formed term. This is not a claim that every CFG is structured. A
Böhm–Jacopini program transformation with auxiliary state is a different claim
from structural graph isomorphism.

## Certificates preserve their data

`Region.Certified.BasicBlock` carries segment, entry, exits and a BB proof under
a fixed model/image/interface. `WithGraph` carries a region row, a graph,
separate validity proofs and an agreement proof. `WithCFG` specializes to the
existing `Tree.FlatCFG`; its agreement requires equal entries, support-label
interpretations and exit sets. Existing `CertifiedSegmentRow` and `CertifiedRow`
remain the graph-free region certificates.

`Refines M N` means pointwise inclusion of all five positive judgment shapes.
Here the arrow transports a proof from M to the more permissive N; some semantic
refinement conventions orient the word in the opposite direction. BB and
graph-certificate transports preserve their underlying data, satisfy identity,
and compose. Graph-property weakening is a separate explicit implication.
No operational graph soundness follows unless the chosen `graphValid` predicate
requires it. Carrier-changing transports need further coherence and are not
claimed here.

`cfgView` observes **all** flat-CFG successors, independently of dominator arcs.
`stateView` retains full transition-system states. `labelGraph` existentially
projects states by PC; it can introduce paths with no consistent state witness.
Different region families need not determine a unique actual CFG.

## Target problems and the meaning of termination

`Region.Queries` supplies normal first-exit targets: one label, one label and
exact state, one label and state predicate, or a label set. The APIs differ:

| Query | Meaning | Divergence / halt / stuckness |
| --- | --- | --- |
| `partialWP` | every finite normal first exit satisfies the target | permitted; may be vacuous |
| `mayWP` | some finite normal first exit satisfies the target | other runs may fail or diverge |
| `mustWP` | starts inside; partial WP; internal accessibility and progress; no reachable internal halt | rules out internal divergence, stuckness and distinguished halts |

`must_implies_may` constructs an exit using accessibility and progress;
`must_implies_partial` retains its universal target guarantee. This is a demonic
must-exit criterion; no fairness is assumed. Normal exits are nonterminal
boundary transfers. `PartialHoare` still separately handles distinguished
halt/return/trap outcomes; `of_partial_hoare` forgets those observations to a
normal-target query. Exact-state/predicate targets imply label targets, singleton
label sets specialize to one label, and partial/may queries weaken postconditions.
`partial_weakest` characterizes the universal admitted-state precondition.

`region` quantifies over an explicit admitted domain. `atEntry` restricts that
domain to an explicit entry PC; it still requires the operational context.
It does not derive semantics or support from a label. Empty admitted domains
make region-level queries vacuous; callers requiring nonvacuity supply a witness
(as existing semantic `Valid` does). A target must lie outside the chosen support
to be a first exit. Exact state equality includes all state components selected
by the client, including memory/frame/interface state when those are modeled.

`Queries.Examples` reuses the existing diverging loop: every conditional target
holds while may-exit and must-exit fail. A nondeterministic fork has a may-exit
witness for label 1 but fails the universal target because it can exit at 2.

## Abstract effect bounds

`Region.Effects.envelope T A U observe` joins observations of every `MayEffect`
from an admitted internal prefix and its next internal or boundary-crossing
step. This includes finite prefixes of divergent runs. In any complete lattice
of observations it is the **least sound upper allowance** (`envelope_le_iff`),
not a greatest set of sound region judgments and not a must-effect result.
Top is always a sound bound. No decidability, computability or enumeration is
required; the definition is noncomputable in general.

`covered_bound` proves a region bound from coverage of all actual steps whose
source is inside support. `labels_bound` joins label-local bounds over the
support. The premises quantify over all inside source states, stronger than
reachable-state-only coverage. No partition into valid BBs is required.
Calls and abnormal effects contribute only when the supplied transition system
emits their events; halt-only observations require an explicit policy/encoding.

The [indexed effects guide](region-effects.md) explains the open family
`Atom Payload`, per-category projection and renaming, direct instruction effects
versus call summaries, and certified terminal control summaries. `UseDef`
remains a sequential transfer with definite definitions; selection has the
proved least-upper-allowance property in its mixed precision order.
`outcomeEnvelope` additionally includes reachable distinguished halts, including
faults or UB represented as halts without emitted events. The checked examples
cover heterogeneous payloads, use/def ordering and an otherwise silent fault.

`MustOccur` instead quantifies over a **chosen nonempty family of finite traces**.
Its witness prevents vacuity, but the family need not include every maximal or
divergent run. `must_implies_may` therefore separately requires coverage of
that trace family by operational `MayEffect`. No must-effect analysis of all
infinite executions is claimed.

## Build and remaining integration boundaries

```sh
lake build --wfail \
  Silmaril.Logic.Fragments.Institution.Thms \
  Silmaril.Logic.Graph.Examples.Thms \
  Silmaril.Semantics.Region.Certified.Thms \
  Silmaril.Semantics.Region.Queries.Examples.Thms \
  Silmaril.Semantics.Region.Effects.Examples.Thms
```

Pass these same targets as `CHECK_TARGETS` to `make check` for the scoped source
and regression gates. This is not a full native release-suite run.

| Further obligation | What is needed |
| --- | --- |
| ELF region/CFG viewer and graph tab | Exporter/schema integration in the actual project explorer; stable row/image/context identity, provenance, stated vs certified status, overlap/disagreement comparison. Missing certificate must remain unknown. No viewer changes are included in this abstract layer. |
| Byte-grounded ELF CFGs | Intrinsic byte/fetch/decode relation and concrete byte provenance, independent of execution; a separate theorem tying edges to actual operational semantics with executable-code immutability, fetch faults and interference policy. Abstract graphs here prove no machine edges. |
| Wasm operational coverage / validated byte map | Connect the existing CFG extraction to execution coverage; validate decoder byte boundaries per body, function index and instruction offset. An asserted map alone is not validation. |
| x86 placement and calls | Bridge verified decode/fetch through executable ELF placement; explicit summary validity and return/resumption conditions for each supported call. Unresolved transfers stay unknown. |
| Carrier/label-map certificate transport | Row mapping, region-proof implication and graph/boundary coherence together; current proof transports preserve the same data/carriers. |
| Richer graph relationships | Directed minor convention, minor transitivity, independently grounded structured-lifting theorems and non-discrete model categories, if needed. No unconditional graph reconstruction from regions. |
| Concrete effect inference | Per-instruction/call/syscall event soundness and step coverage for the selected ISA/interface, including concurrency assumptions when applicable. No multithread soundness is implied by syntax. |
