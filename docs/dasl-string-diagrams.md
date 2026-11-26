# Portable DASL string diagrams

`string-diagram/v1` stores a finite directed wiring with ordered boundary
ports, ordered box occurrences and ordered ports on every box. Box labels are
arbitrary shallow DASL values. The same object can be checked against a
signature, interpreted with a fixed evaluation order, or used with a
quotient that permits interchange. A reader needs the selected profile and
signature to assign a categorical meaning.

The core uses Silmaril's [abstract DASL model](atproto-dasl.md) and
[codec contracts](atproto-dasl-encodings.md). Its positional identifiers are
like the indices of the [WAC composition format](dasl-wac-graph.md). Here a
position identifies an individual port, and forward references are meaningful
in the raw topology.

## Core schema

The object is exactly `["string-diagram/v1", [n, m, boxes, inputs, exports]]`.
Every array shown has the specified order, including empty arrays.

| Field | Domain |
| --- | --- |
| `n, m` | Number of diagram inputs and exports, respectively |
| `boxes` | Ordered array of `[p, q, data]`, with `p` input slots and `q` output ports |
| `inputs` | Flat array of source ordinals, one entry per **box input slot** |
| `exports` | Array of source ordinals, one entry per **diagram output slot** |

The two source tables record where each destination reads from. There is
no source entry for a box output port or a diagram input port. A box output
is addressable as a producer even if nothing reads it.

All counts and ordinals are nonnegative DASL I64 values. Write $B$ for the
box count, $p_b,q_b$ for the two arities of box $b$, and set
`K = sum(p)`, `N = n + sum(q)`. Check `B, K, N ≤ 2^63 − 1` using
mathematical integers or checked arithmetic. Require `len(inputs) = K`,
`len(exports) = m`, and every entry in either table in `[0,N)`. The
constructor arities above and the version tag are exact. If $N=0$, both
tables must be empty. Nonnegative signed I64 values are detectable even
when the DASL library stores I64 bits as `UInt64`.

The offsets are exclusive prefix sums. The sources and destinations are
disjoint, even where they use the same numeral.

| Endpoint | Range of local slot | Position |
| --- | --- | --- |
| Diagram input `In(i)` | `0 ≤ i < n` | `i` in source space |
| Box output `Out(b,j)` | `0 ≤ j < q_b` | `n + sum(q_a for a < b) + j` in source space |
| Box input `Arg(b,k)` | `0 ≤ k < p_b` | `sum(p_a for a < b) + k` in `inputs` |
| Diagram export `Export(e)` | `0 ≤ e < m` | `e` in `exports` |

Thus the core consists of an ordered header and a total function from
destination slots to source ports. The offsets for the output blocks
partition `[n,N)` into half-open intervals. Each ordinal belongs to one
nonempty interval and subtraction of its left endpoint gives the local
index. The same argument partitions the flat input table over `[0,K)`.
Empty intervals contribute no positions, and the header still records
their boxes. This gives the two inverse index translations.

A box label is the original [shallow DASL tree](atproto-dasl.md), including
inline containers, bytes, and typed object or raw links. The diagram
decoder need not dereference links and reads no arity, centrality, or type
information out of label fields. Structural validation accepts repeated
labels and sources, unused sources, through wires, nullary boxes, forward
references, and cycles. A bare cycle made of an identity wire needs the
separate trace field below.

## Lossless layouts

Fix a valid core and use the endpoint sets and order specified above.
The inverse maps below are exact on their stated domains. A reader
rejects a broken invariant before applying the inverse. Derived tables
with an implementation-dependent row order must be sorted by their keys
for a canonical serialized view.

| Layout | What is stored and checked | Inverse and reason |
| --- | --- | --- |
| Box-local input tags | Keep the boundary counts and exports. For each box store its output count, label and ordered vector of source tags, such as `["in",i]` or `["out",b,j]`. Its input count is the vector length. A scattered variant uses destination keys `(b,k)` and retains the input counts, with each key present exactly once. | Translate every source tag through the source partition and concatenate in box-major order. Split on the saved widths to invert. Empty groups are reproduced. In the scattered variant sorting by the destination keys recovers the same vectors. |
| Separate label array | Keep `[(p_b,q_b)]` and one label per box in the same order, with equal widths. | Zip at box index. Unzipping is its inverse at each index, preserves length and keeps repeated labels. |
| Structure of arrays | Use `[p_b]`, `[q_b]`, `[data_b]` of equal length. An alternative uses the two prefix arrays, each of length `B+1`, starting at zero and nondecreasing. Keep all equal adjacent offsets. | Pointwise zip, or take adjacent differences first. Differences of the partial sums give the arities and summing the differences telescopes back to the offsets. Boundaries and the two destination tables are unchanged in both column layouts. |
| Port/box incidence plus edges | Store boxes with ordered identities and labels. Store all endpoints and the port-to-box incidence with role and local position. Boundary endpoints have roles and positions of their own. Edges relate sources to sinks, with a unique incoming edge for every sink. Check that local slots and boundaries are dense. | Count the port rows at each box and boundary, then write each edge's source at the position of its sink. Regenerating endpoints from the resulting arities and positions and regenerating edges from both tables give back these relations. Surrogate identifiers are recovered up to renaming unless also stored as an identity map. |
| Endpoint incidence only | Use unordered blocks of tagged endpoints, each containing exactly one source and zero or more distinct sinks. Every source and sink occurs in exactly one block. Keep the ordered header (or the complete endpoint universe plus labels and the ordered box table). This is incidence with anonymous wire identifiers. | Associate each sink in a block to its sole producer. Conversely group sinks by their table value and include every source as a block, including singleton sources. Two distinct blocks cannot share a producer, so regrouping gives the original partition. An equivalent sparse view omits singletons when the complete source universe is supplied. |
| Direct quad edges and label table | Use `(sOwner,sSlot,tOwner,tSlot)`; a role-specific boundary owner sentinel `-1` means input on the source side, export on the sink side. Nonnegative owners are box indices. Keep `n,m` and rows `(p_b,q_b,label)`, with label inline or by index. Check every endpoint and require each sink key exactly once. No separate port rows. | For each quad use the producer partition and write the source ordinal at the destination position. Enumerating the two tables and taking their inverse endpoint translations recovers the quad relation. Quads sorted by `(target kind, owner, slot)` with box inputs first recover one exact sequence. |

An interned label pool consists of distinct shallow labels and one
index per box. To make the pool invertible as a layout, include only used
labels in first occurrence order, with exact shallow equality for
interning. Expansion and reinterning then assign the same indices by
induction over box positions. An arbitrary pool can contain unused rows or
noncanonical order and requires retaining the pool and indices to recover
those choices. An inline label and a link to a block containing that label
are different shallow labels.

The header is necessary in general. With edges alone even the empty
quad table can stand for the empty diagram, one unused diagram input, or
a labeled `0 → 0` box. Slot maxima in observed quads miss trailing unused
outputs. Unordered port membership loses argument order. A set of
`(source box, target box)` pairs loses multiplicity and all port indices.
Boundary positions or a boundary identity map are needed to distinguish
an identity wire from a boundary permutation. A thin layout is
invertible only under conditions that uniquely determine every omitted
field, such as an externally fixed labeled header. These maps transport
typing, ordering, loop, placement and display extensions unchanged when
IDs are positional, and along the endpoint and box bijections when they
use other IDs. A view that drops those tables recovers only the core.

## Validated profiles and typing

A validation profile specifies an independent choice of wiring geometry,
scheduling, wire usage, and a signature. It can be attached in an outer
object with a versioned profile identifier. A base reader can handle
`string-diagram/v1` without any such agreement. A reader interpreting
a profile needs to validate its refinements as well as the core. The
extension layouts below specify independent refinements of the core.

A signature over colors $C$ is a relation
`Admits(data, A, B)` on a shallow label and a pair of finite ordered
words over $C$. A unityped signature has one color and its shapes are
just pairs of arities. A typed signature uses words, so boxes of the
same arity can have different types. A signature can be single-shape
(a partial function from label to shape), finite overloaded (a table of
admissible shapes per label), or relational. Even in unityped mode a
profile may constrain arity by label. A maximally permissive unityped
signature freely gives each `(data, p, q)` its own generator.

Every v1 profile uses exactly one generator for each admissible
`(data, input word, output word)` in a fixed signature. The label is
compared by exact shallow equality and the words by their canonical
color identifiers. In unityped mode the words are determined by the
two arities, so the key is just `(data, p, q)` within the signature.
Different admissible shapes for one label still give different
generators. A signature with distinct generator identities at the
same label and shape is outside the v1 interpretation. Validation
of a finite signature with explicit generator rows must check this
uniqueness before interpreting diagrams. The raw core can still be
read as data.

The generator key is scoped to the signature. Use its exact object
link in a content-addressed context, such as the signature link of a
theory. The raw core and typed wrapper take that context from the
profile in which they are read. The same bytes can be used with
different signatures. A typed isomorphism or replay judgment fixes
one signature for both operands.

An explicit typing records a length-$N$ array `sourceTypes` and the
ordered boundary type words. Use shallow DASL type identifiers with
exact equality, or canonical identifiers in a referenced type table.
For each destination, its type is `sourceTypes[source]`. Require the
diagram input word to equal the first $n$ source types and the export
word to equal the $m$ looked-up types in order. For each box, take the
types of its inputs by lookup and the types of its outputs from its
source block and check `Admits`. Types of unused sources are still
specified. In unityped mode the color array is redundant. An equivalent
explicit representation records both producer and destination types and
requires type equality along every edge. A typed transport can use
`["string-diagram/typed/v1", core, sourceTypes, inputTypes, exportTypes]`.
Signature and type normalization, if any, are part of the agreed profile.

Intrinsically a box carries a generator with indexed source and target
words. Boundary and box input slots have types; each wiring value is a
source with a proof that its type equals the destination type. Equivalently
use a dependent finite function taking each destination to the subtype
of sources of that color. An explicit valid typing determines the
unique v1 generator at every box. Construct the intrinsic data by
pairing each ordinal with its typing proof. Erasing the proof fields
recovers the explicit data. Constructing again gives the same intrinsic
data up to proof irrelevance. Erasing the types as well is generally
many-to-one.

A future opt-in generator identity extension can use
`["string-diagram/generator-ids/v1", body, generatorIds]`.
Its profile would require a length-`B` array of nonnegative I64
indices into the linked signature's generator rows, including for
unityped boxes. The indexed signature row must match the label
and recovered shape at that box. Layout conversions must
transport this column with box occurrences, and graph extraction,
isomorphism and replay in that profile must retain and check it.
Readers that support the base v1 profiles can preserve the new wrapper
opaquely. Interpreting it requires a verifier registered for that
extension.

For inference, introduce a variable for each source and substitute the
same variable into all its uses. A fixed boundary contributes equations.
A single-shape signature fixes the variables' colors and detects
inconsistent constraints by comparing assignments to each variable.
Finite overloaded signatures give a finite constraint problem when the
candidate type domains are finite. Unused through variables or feedback
components can remain unconstrained. Backtracking over the finite choices
is sound and complete by enumeration, with potentially exponential
cost. Arbitrary relational signatures supply neither a decision
procedure nor a principal typing theorem. A unique assignment gives a
unique elaboration with a label-and-shape signature. For multiple
solutions, coherence would require a specified erasure interpretation
and a proof that all solutions have equal denotation in it. Even a
single `0 → 1` label with outputs of different colors can have distinct
interpretations. Distinct overloads need distinct generator interpretations
unless an equation expressly identifies them.

## Acyclicity, scheduling and equivalence

The dependency multigraph has one vertex per box and an edge `a → b`
for every input of $b$ sourced from an output of $a$. Count self-edges
as cycles. Boundary sources and destinations contribute no box dependency.
Acyclicity means this graph admits a topological order. In a forward
encoding every such source belongs to an earlier box, so the row order
is itself topological. A DAG can be written forward by renumbering boxes
and all references with a topological order. This renumbering changes
the raw value and requires transporting extensions.

The categorical constructions below use finite diagrams with unbounded
natural indices. A fixed I64 transport bound gives a representable
subset. Composition and tensor in the abstract syntax can exceed that
bound. Monoidal tensor juxtaposes two disjoint copies and concatenates
their ordered interfaces. Composition at a matching interface substitutes the
first diagram's export source for every reference to the corresponding
second diagram input, with disjoint box identities and the outer
boundaries retained. Identity pairs each export with its corresponding
input. Renumbering into the result's table order gives the core
operation. The structural wire-use profiles are closed under these
operations. On a composed wire the number of downstream uses replaces
the use at the cut export. Replacing exactly one use by exactly one, at
most one by at most one, or at least one by at least one preserves the
respective condition. In the acyclic profiles all new dependencies go
from the first operand to the second.

**Symmetric monoidal.** For acyclic linear wiring and a colored generator
signature, incidence is the usual combinatorial presentation of the free
strict symmetric monoidal category, with objects color words (a PROP in
the single-color case). At a fixed signature the quotient is by a box
bijection preserving generator keys, ordered local slots, wiring, and
each boundary position. There are no distinguished local
coordinates. Here and below linearity counts **all** consumers, including
exports.

To see the presentation, choose a topological order. At each step permute
the live frontier so the next box gets its ordered inputs, apply that
generator with identities on the rest, then give fresh sources to its
outputs. Finish with the unique permutation determined by the export
slots. Linearity ensures that every input is available and used once and
the final frontier contains precisely the exports. Different choices of
frontier ordering cancel by symmetry coherence and naturality. Two
topological orders are joined by adjacent swaps of incomparable boxes
(move the first desired box left past the intervening boxes and induct).
Their live inputs are disjoint, so the swapped steps agree by interchange
and symmetry. Conversely composition as gluing, tensor as concatenation,
and structural symmetry as a permutation preserve the port-incidence
interpretation of the symmetric monoidal equations. Gluing the serialized
steps recovers the wiring. This gives inverse presentations, before any
generator equations. The universal interpretation sends each generator to
an arrow of the declared shape and evaluates the steps; the argument
makes it independent of the witness order.

**Symmetric premonoidal.** For the acyclic linear profile, use a forward
encoding whose row order is a selected execution schedule. In a strict
presentation, tensoring with an object on either side is functorial.
For `f : A → B` and `g : C → D`, executing $f$ first gives
`(f ▷ C); (B ◁ g)`, and executing $g$ first gives
`(A ◁ g); (f ▷ D)`. Interchange for these two composites is a further
equation. Central arrows commute with every arrow in the interchange
squares, in both tensor positions. Structural permutations must be
central in the target of this profile.

With a classification into distinguished central and other generators,
the scheduled symmetric syntax equates adjacent dependency-incomparable
steps when at least one is qualified central. The qualification may
be by `data` (all admissible shapes of that label) or by the scoped
`(data,shape)` key. Declaring an arbitrary payload central requires
evidence from the signature or denotation.
Exact equality of labels carries no such evidence. A target may
validate extra interchanges by its equations or a proved independence
relation; those can be recorded as theory equations. The monoidal
profile qualifies every generating step. In a premonoidal setting this
gives a monoidal interpretation within the center, or every arrow of
an admitted monoidal target may already interchange.

An equivalent order witness for this syntax is the total order on the
nonqualified boxes plus the dependencies. Add a chain of precedence edges
through the nonqualified boxes in that order, and require the union to be
acyclic. Its linear extensions have the same effect order. The adjacent
swap argument applies to this union order. Incomparable boxes in the
union cannot both be nonqualified, so each swap is allowed. Conversely
an allowed swap preserves all dependencies and the nonqualified order.
Up to the same box bijection, this characterizes the scheduled quotient.
For a free symmetric premonoidal interpretation with a specified central
part, read each schedule as a sequence of whiskered generators and
central permutations. Composition concatenates schedules and whiskering
adds untouched wires on the selected side. A whiskering can be moved to
the individual steps by functoriality. Structural coherence moves
permutations to the frontiers, where the sequentialization argument for
the monoidal case applies with just the permitted swaps. Conversely
the premonoidal structural equations preserve incidence and noncentral
order. The resulting presentation is for the specified symmetry and
centrality equations. The unrestricted center of
a quotient or model may include more arrows than the designated part.
The runtime presentation has a [nullary center obstruction](../Silmaril/Semantics/RuntimeWires/Nullary/Thms.lean).

**Planar and braided.** A wiring might require a crossing, as with the
two-wire swap and no boxes. Even planar realizations of one wiring may
be inequivalent. A nullary scalar to the left of a through wire and the
same scalar to its right give the same core. The repository proves
seam inequivalence of this pair in its [slice model](../Silmaril/Semantics/RuntimeWires/SeamPlacement/Thms.lean).
Use a planar word or a progressive slice witness. A sequential slice
row is `[b, g]`, with nonnegative I64 box and gap indices. The
index `g` refers to the current ordered frontier of live source
occurrences. Require `b < B` and `g + p_b ≤ len(frontier)`.
Split the frontier as `L · U · R` with `len(L) = g` and
`len(U) = p_b`. The occurrences in `U` must match the box input
source ordinals in slot order. Replace exactly that block, at the
same cut, by the fresh output occurrences `V` in output-slot order.
In `L · U · R → L · V · R`, the prefix `L` and suffix `R`
carry the same untouched strand occurrences in the same order.
Check the generator's input and output types when
typed. When `p_b = 0`, `g` selects one of the
`len(frontier) + 1` indexed gaps, even for a scalar with no outputs.
For the progressive linear witness start with the ordered diagram
inputs, step through every box exactly once, and require the final
frontier to equal the export source table in order. The free strict
monoidal (non-symmetric PROP in one color) reading uses the typed
planar terms or progressive diagrams modulo the monoidal coherence
laws, with the core as their forgetful image. For a planar premonoidal
reading retain the positions and allowed moves or keep the runtime wire
explicit, as in the [runtime-wire presentation](../Silmaril/Semantics/RuntimeWires/Presentation/Thms.lean).

In the braided case retain a typed braid word between slices, with
signed crossings (or explicit crossing generators and braid equations).
A two-strand positive crossing and its inverse have the same boundary
permutation; the square of the positive crossing has the incidence of
the identity. Braid relations preserve the accumulated signed crossing
number in the two-strand example. The core models only the symmetric
forgetting of the braid. In all cases flattening erases coordinates,
lengths, straight-wire subdivisions, simultaneous placement, and
crossing over/under data. It erases relative left/right placement where
incidence does not force it. The symmetric equivalence is the coherence
quotient for progressive symmetric diagrams. Ambient isotopy of planar
or braided drawings has the additional invariants just described.
For geometric hypotheses underlying the free constructions see
[Selinger's survey](https://arxiv.org/abs/0908.3347) and [Joyal and Street](https://doi.org/10.1016/0001-8708(91)90003-P).
For the premonoidal geometry and runtime construction see
[Román and Sobociński, v5](https://arxiv.org/abs/2305.06075v5).

**Trace.** In the linear symmetric traced profile permit box cycles and
add a list of standalone wire loops, each with its color (use `null` in
unityped mode). For transport use `["string-diagram/trace/v1", body, loops]`,
where `body` is a core or the explicit typed wrapper, according to the
profile. Each loop type uses the same type identifier domain as the body.
For equivalence use the multiset of colors of the standalone loops. This
retains `Tr_X(id_X) : I → I` as a scalar, including its multiplicity.
Setting the list to empty forgets real information. Boxless components
with exposed boundary are still represented by ordinary through wires.

For the free symmetric traced reading, cut box-to-box wires to get a
DAG, routing each cut producer to a fresh export and each cut consumer
from a fresh input of the same color, in matching order. Cutting all
such wires always suffices. Each standalone loop is an extra matched
input/export pair joined by identity. Interpret the DAG and trace over
the appended color word. Conjugating the feedback positions by a
permutation is dinaturality; adding cuts on remaining internal wires
gives the same interpretation by yanking and the composition,
superposing and vanishing laws. One can compare different cut sets at
their union by these moves. Conversely wiring interprets the trace laws
by gluing the paired boundary slots and contracting through-wire
segments, counting any closed segment as a loop. For example, yanking
the two-wire symmetry over one wire leaves an identity through wire,
whereas tracing an isolated identity leaves one closed component.
This is the symmetric traced presentation, with full trace in the
target. For general planar or braided feedback the geometry and the
chosen trace structure matter. For cycles with sharing or deletion,
explicitly elaborate copy and delete in a target with a suitable trace
before applying the linear trace construction. Feedback for
premonoidal computations requires a model and laws, for example guarded
feedback or a specified iteration operation, with its own well-formedness
and equivalence.
See [Joyal, Street and Verity](https://doi.org/10.1017/S0305004100074338)
and [Kissinger](https://arxiv.org/abs/1308.3586) for traced categories and
combinatorial presentations.

## Use counts and structural semantics

For a source $s$, let `uses(s)` count its occurrences in the
concatenation of the two source tables. This includes zero for any source
not present in either table.

| Usage | Condition | Implicit operations in a symmetric interpretation |
| --- | --- | --- |
| Linear | `uses(s) = 1` for all $s$ | Identity wiring |
| Affine | `uses(s) ≤ 1` | Chosen deletion `X → I` |
| Relevant | `1 ≤ uses(s)` | Chosen copying `X → X ⊗ X` |
| Unrestricted | Any count | Both operations |

To elaborate, list each source's sinks in a fixed order. For zero sinks
attach a deletion, for one use the wire directly, and for $k>1$ attach
an iterated copier with $k$ leaves, connecting each leaf to its sink.
For equivariance under changes of leaf order and tree, require a
cocommutative coassociative copying operation (and symmetry). With
deletion require the appropriate counit laws if copy and delete may be
simplified together. An induction using coassociativity sends any copy
tree to the right-associated tree, cocommutativity produces all adjacent
leaf swaps, and counitality eliminates deleted branches. This justifies
the implicit sharing convention for these chosen structural operations.
In a planar setting, grouping a source's sinks may require a placement
witness or explicit copy/delete generators. In a premonoidal target any
move of a structural operation across effects needs centrality or a
justified scheduling law.

These structural operations can be supplied on the generating colors
and extended coherently over words by tensor, symmetry and the unit.
This presents wiring with local commutative comonoid equations when both
operations are available, or the indicated copy-only or delete-only
laws. For an affine category in the terminal-unit sense require
natural deletion with the
unit law. For a relevant reading with natural diagonals require
naturality, tensor compatibility and the unit law for copying. A
cartesian target has both coherent natural operations, with the
commutative comonoid laws; a free cartesian interpretation imposes
those equations on the syntax. It may identify different cores:
natural deletion can erase a dead pure box, natural copying can
identify a result shared across two uses with two evaluations of a
pure computation. An effectful producer whose output has two uses is
still executed once by the sharing interpretation. Counitality,
naturality, effect independence, trace and any user equations must be
stated at the chosen semantic boundary. These are distinct from
accepting a use-count profile.

## Graph objects and extraction

The proposed graph codecs use the following exact tagged tuples.

| Object | DASL tuple |
| --- | --- |
| Directed multigraph | `["directed-graph/v1", vertices, edges]` |
| Directed hypergraph | `["directed-hypergraph/v1", vertices, hyperedges]` |
| Open multigraph | `["open-directed-graph/v1", graph, domain, codomain]` |
| Open hypergraph | `["open-directed-hypergraph/v1", hypergraph, domain, codomain]` |

The inner object of an open variant must have the corresponding closed
tag. `vertices` is an ordered array of shallow DASL labels. An edge is
exactly `[tail, head, data]`, with `tail` and `head` each a vertex index.
A hyperedge is exactly `[tails, heads, data]`, with ordered arrays of
vertex indices. The data field is a shallow DASL value. All structural
array lengths must fit in nonnegative I64. For $V$ vertex rows, every
vertex index is an I64 in `[0,V)`. Parallel edge rows retain separate
occurrences, even if their data agree. Self-edges and repeated indices
within or across hyperedge endpoint lists are legal. Empty lists,
including both lists of a nullary hyperedge, are legal. With no vertices,
ordinary edge rows are impossible and every hyperedge endpoint list is
empty.

`domain` and `codomain` are arrays of vertex indices into the same
table. These define functions from the position sets
`[0,len(domain))` and `[0,len(codomain))` to `[0,V)`, respectively.
They can repeat or share vertices. The two position sets distinguish
boundary roles even when their legs map to the same vertex. Isolated
vertices remain in the table. Injectivity, typing, linearity and
acyclicity are additional profiles.

- The **box hypergraph** has wire vertices indexed by sources. Each
  box is a labeled directed hyperedge whose tail is the sequence of
  its input sources and whose head is the sequence of its output
  sources. The left boundary leg enumerates $0,\ldots,n-1$; the right
  boundary leg is the export table. Retain all vertices, even when
  unused, and all hyperedges, including nullary ones. The ordered
  variant recovers the core if every wire vertex is produced exactly
  once by the left boundary or an output position, and the core's
  count and sum bounds hold. The inverse enumerates producers by
  taking the domain followed by the concatenated heads. This order
  is a bijection from source ordinals to vertices. The inverse reads
  each hyperedge's arities and uses the inverse bijection on the
  concatenated tails and the codomain. Encoding back recovers the
  incidence up to that vertex renaming, with hyperedge and leg
  positions fixed. For an exact round trip into the bare core, use
  source order for vertices and `null` vertex labels. In the typed
  box-hypergraph profile, label each wire vertex with its canonical
  color ID, including for unused sources. In the inverse, the producer
  enumeration recovers `sourceTypes`, the two legs recover the boundary
  words, and each hyperedge's tails and heads recover its shape. At a
  fixed signature the edge label and that shape determine its v1
  generator, including in unityped mode. In source order, this recovers
  the explicit typed wrapper exactly. Arbitrary extra vertex data
  needs a side table. Dropping hyperedge order gives the symmetric
  incidence quotient up to boundary-fixing isomorphism and forgets a
  selected schedule. Open hypergraphs with
  multiple producers, undriven vertices, or repeated left legs lie
  outside this image. Feedback without vertices needs a separate loop
  multiset, or a graph convention with marked loop vertices.
- The **box dependency graph** keeps the box vertices and their input
  dependencies. A port-labeled multigraph augmented with the ordered
  header, boundary incoming and outgoing incidences and through wires
  is the quad representation. Its plain projection drops endpoints,
  and a simple graph also merges multiple edges. An **ordering graph**
  can add effect precedence arcs distinctly from value edges. Plain
  reachability gives a partial order for a DAG and drops direct edge
  witnesses; even the transitive reduction cannot recover them in
  general. For instance, `a → b → c` and its augmentation with
  `a → c` have identical reachability. Removing isolated vertices
  also loses nullary actions and unused-boundary information.
- Isomorphisms of graphs and hypergraphs are bijections on vertices and
  edge occurrences preserving data, ordered incidence and each leg
  position as appropriate. For typed box hypergraphs, compare at the
  same signature and preserve wire colors and exact shallow edge labels.
  Ordered tail and head preservation then preserves the shape and
  hence the generator key. Dependency graph isomorphism does not lift
  in general. Incidence isomorphism with the ordered box header fixed
  is raw structural equality after ordinals are reconstructed. An
  unordered symmetric diagram can use colored graph isomorphism by
  reifying boxes and ports, with colors or gadgets for each role,
  local position, boundary identity, type, label, and precedence edge.
  Include standalone loop colors in the comparison. A graph normal form
  needs a stated canonical labeling algorithm; topological sorting
  alone does not give one invariant under all renamings.

A flat dataflow or straight-line SSA fragment can map produced values to
source ordinals and uses to slots. CFG edges carry transfer and block
argument information, including terminator choice, joins, and dominance;
a box dependency graph loses it. A CFG transport needs a separate
block/region or edge-kind table and a binding/scope contract. RVSDG-style
hierarchical alternatives and loops can use linked subdiagrams together
with typed region interfaces. A proof DAG can interpret premises as
ordered inputs and conclusions as outputs, with contexts, binder scopes,
rule admissibility and proof-checker semantics supplied separately.
An arbitrary cyclic graph does not certify a cyclic proof's progress
condition. Compare the [SSA](projects/ssa.md), [PEG](projects/peggy.md)
and [DASL proof syntax](dasl-logic-syntax.md) developments.

## Storage and indices

Canonical DRISL already encodes nonnegative I64 arguments compactly.
The core needs $O(B+K+m)$ integer cells and $B$ labels. It need not
enumerate all $N$ sources. Array and label framing, integer widths,
and encoded payload sizes contribute separately to byte costs. Use
the existing [canonical DRISL adapter](atproto-dasl.md#contracts), including
its selected CID profile, value restrictions and serializer bounds.
A packed variant can use
`["string-diagram/packed-le64/v1", [n,m,B,pBytes,qBytes,labels,inputBytes,exportBytes]]`.
Each byte column is a concatenation of exactly eight-byte little-endian
unsigned cells, with high bit zero. Require `len(labels) = B` and
byte lengths `8B, 8B, 8K, 8m` for the four columns, respectively.
Check all products before allocation and apply the core guards after
unpacking. Splitting into eight-byte cells and taking their unsigned
values inverts packing because every admitted value has a unique
eight-byte representation. This layout trades compact small integers
for constant-time indexed reads. A separate variable-width profile
could make a different trade, with specified minimality and offsets.
Use native byte strings for packed cells, or version a separate raw-link
profile for byte chunks.
Object links to paged DASL columns are also possible. Record chunk
lengths and boundaries, check every resolved page against its declared
length and range, and distinguish missing from invalid. See
[DASL index sequences](dasl-index-sequences.md) for existing ordered
and paged codec conventions. These extension encodings have different
DASL values and content names.

Under a word-RAM cost model, building prefix arrays and validating
counts/ranges from materialized arrays costs $O(B+K+m)$ time.
Computing an ordinal from a local slot is $O(1)$ with prefix arrays.
Finding the producer of a global ordinal uses the last prefix at most
the ordinal in the output block ($O(\log(B+1))$ for box outputs),
or $O(1)$ with a dense owner table costing $O(N)$ space and time.
Scanning source counts with a dense consumer array takes
$O(N+K+m)$ time and can also build reverse adjacency (offsets and
an array of sink identities). Sparse counting uses $O(K+m)$ expected
time with hashing or $O((K+m)\log(K+m+1))$ by sorting. For checking that
all sources occur, the number of distinct valid keys must equal $N$.
Building dependencies takes $O(B+K)$ time using dense owners, **after**
paying $O(N)$ to build them, or $O(B+K\log(B+1))$ with prefix lookup.
Kahn sorting or SCC detection then takes $O(B+E)$, where $E\le K$ is
the number of box dependencies including multiplicity. In a forward
profile, a box input must have source ordinal below the start of that
box's output block and a single scan suffices. Label parsing, type
equality, signature queries, incidence isomorphism and model evaluation
have their own costs.

A normalized relational storage design uses the following keys. Every key
is in a diagram scope, or a revision scope for mutable stores.

| Relation | Key and values |
| --- | --- |
| Diagram | `diagram` with boundary counts and profile/version reference |
| Box | `(diagram, box)` with row position and label key or inline data |
| Boundary | `(diagram, role, position)` with optional stable identity |
| Port | `(diagram, box, role, slot)` with optional type |
| Source and sink | Role-tagged slot keys pointing to either a boundary or a port |
| Wire | Sink as primary key and foreign key to Sink, with a foreign key to Source |
| Label | Pool key with a shallow DASL value, with optional exact-value dictionary |

Enforce dense positions and local slot ranges, unique row positions
and complete sink coverage across the committed instance. Foreign keys
check endpoint existence and diagram scope. Total sink coverage and
cross-row arity checks need transaction-level validation or equivalent
constraints. Derive counts from dense port rows or keep them as checked
materialized columns. Index wires by source for consumers and by sink
for a box's ordered operands and export lookup. A quad relation with
arities and boundary counts is a smaller normalized alternative when
individual ports carry no further data. A scheduled dependency index
can retain wire and precedence edge kinds and source-port provenance.

Future extension tables can include the following records, with ID
translations applied when extracting subdiagrams or reordering boxes.

| Table | Purpose |
| --- | --- |
| Signature, types and shapes | Label and shape admission, colors, boundary profiles and selected shapes. An opt-in generator ID extension uses a separate box column. |
| Order, geometry and trace | Effect sequence, planar gaps/slices, braid words, feedback cuts, and standalone loops |
| Theory and refinement | Theory equations and the evidence records specified below |
| Origins and display | Stable box/boundary IDs, spans, titles, styles, region paths, coordinates, chosen layout and renderer hints |

Display metadata can be attached to a diagram revision as a sidecar by
box occurrence, never by label alone. Coordinates and styles do not
supply validated planar placement. If a renderer uses positions as a
semantic witness, validate that witness with the relevant geometry
profile. Repeated labels remain independently selectable, and an
interactive renderer can use the source index to highlight uses. A
metadata-sensitive comparison needs an explicit policy and the
transport of metadata along its box and boundary maps.

## Theory, equality evidence and refinement

Byte equality, shallow tree equality, profile isomorphism, and equality
under a theory are different relations. A CID names serialized bytes
under a specific codec and hash policy. Distinct representations of
one diagram may each have a CID.

The following tuples specify versioned proof records. Each named field
in the table is an object link except for the ordered type words,
the equation array, and witness payloads. Object links must resolve
to their declared kind with authenticated bytes under the selected CID
policy. Use exact linked keys throughout a judgment.

| Object | DASL tuple |
| --- | --- |
| Interface | `["string-diagram/interface/v1", inputTypes, exportTypes]` |
| Theory | `["string-diagram/theory/v1", profile, signature, equations]` |
| Equality claim | `["string-diagram/equivalence/v1", theory, interface, lhs, rhs, verifier, witness]` |
| Refinement claim | `["string-diagram/refinement/v1", theory, model, relation, interface, source, target, verifier, witness]` |

An interface contains ordered color words in the signature's type
identifier domain. Use one `null` per slot for a unityped signature.
Its two words must agree with the decoded diagram boundary, including
order and length. Thus both endpoints have the same interface in v1.
A future profile with interface change needs an explicit typed adapter
or a relation schema with two interface keys. An equation is exactly
`[interface, lhs, rhs]`, with linked operands valid under the theory's
profile and signature and at that interface. Equation keys are
nonnegative I64 row ordinals into the immutable theory's equation
array, whose length must fit in nonnegative I64. The list contains
concrete typed equations without metavariables. The theory denotes
the least well-typed congruence containing these equations and the
admitted structural laws, closed under the profile's operations.
Orienting an equation for replay does not change that congruence.
The signature link fixes the v1 generator keys throughout the theory,
its equations, and every checked claim and context.

### Equality evidence

The v1 chain verifier scheme uses
`["string-diagram/equational-chain/v1", steps]`.
Starting with the claim's `lhs`, replay each step against the current
diagram and set the current diagram to its `next` link after successful
validation. The last link must be `rhs`. An empty list therefore
certifies a validated claim with the same endpoint key on both sides.
The scheme recognizes exactly the following two step kinds.

- `["iso", next, boxMap]` checks structural isomorphism. For the
  symmetric incidence profiles, `boxMap` lists one target box index per
  current box and must be a bijection. Check exact label equality and
  equal recovered shapes in the common signature. These checks
  establish preservation of generator keys. Check arities, types at
  every port, ordered slots, wiring after translating producer and
  consumer positions, and both ordered boundaries. Also check the
  noncentral order in the premonoidal profile and loop multiplicities
  by color in the traced profile, as applicable. A placement or braid
  profile requires its own geometric evidence scheme for such a step.
- `["equation", next, row, direction, context]` looks up `row` in the
  theory and takes its sides in the given order. `direction` is exactly
  `"forward"` or `"reverse"`. The verifier reconstructs the current and
  next diagram by placing the respective sides in the same typed
  one-hole context. Both reconstructed presentations must agree with
  the respective decoded diagrams. Explicit `iso` steps can bridge
  different isomorphic presentations.

A context is one of `["hole"]`, `["before", diagram, context]`,
`["after", context, diagram]`, `["tensor-left", diagram, context]`,
`["tensor-right", context, diagram]`, `["whisker-left", types, context]`,
`["whisker-right", context, types]`, or `["trace", context, types]`.
`diagram` is an object link and `types` is an ordered color word.
Before and after specify composition in the indicated order.
Tensor and whiskering place the other operand or object on the
indicated side. Trace closes a matching suffix of the input and
output words against the specified feedback word. Check typing and
the availability of each operation at every constructor. The
verifier scheme fixes the result row order and normalization for
these operations. It must reject overflow of the transport bounds.

This verifier checks a fragment of the full theory congruence.
A structural equation that already evaluates to identical diagram
keys needs no step. Those that evaluate to presentations related by
the checked box bijection can use `iso`. Any other structural law
requires a checked rule in another verifier schema, or a concrete
instance explicitly declared as an equation in the theory table.
With an empty equation table the v1 chain checks only reflexivity
and supported `iso` steps. For example, in an unrestricted
cartesian profile, natural deletion equates a unary box followed
by deletion with direct deletion of its input. The cores have
different box counts and no `iso` step between them. A verifier for
the generic deletion law would have to check its profile and the
reconstructed instance even when the equation table is empty.

Induction over the replay proves soundness for the theory
congruence. The initial diagram is equal to itself. An isomorphism
step uses a structural law of the profile, and an equation step
uses congruence in the reconstructed context. Transitivity yields
the final equality. Soundness in a target model also requires that
the interpretation validate the theory's equations and structural
laws. Replay checks only supplied steps and contexts. The coverage
above makes no completeness claim about matching, search or the
full theory congruence. The repository's
[DASL e-graph bridge](dasl-egraph-bridge.md) uses a related
replay-then-validate contract for class tables.

### Directed refinement evidence

Read the refinement claim as an arrow from `source` (the baseline or
specification) to `target` (the candidate refinement). The relation key
selects a versioned predicate on that ordered pair in the linked
theory, model and interface. A model key fixes the interpretation
and its observation policy. A relation implementation must declare
its direction and domain, and the verifier must validate that the
model supports the theory, relation and interface as required by
that predicate. Model satisfaction of the theory is required if
the predicate is defined on theory classes.

For example, a relation for finite behaviors can require
`Obs(model, interface, target) ⊆ Obs(model, interface, source)`.
One witness format is
`["string-diagram/finite-observations/v1", sourceObs, targetObs]`.
The two observation arrays must encode finite sets in the registered
model's observation domain. The verifier must establish that each
set is exactly the model's observations of the indicated operand,
for example by replaying exhaustive evaluation, then check inclusion.
Checking inclusion of supplied samples alone does not establish
the claim. If a specification can emit either Boolean and a candidate
always emits false on the same interface, a checked refinement from
specification to candidate has observation arrays `[false,true]` and
`[false]`. The reverse claim fails inclusion, even with the two
correct sets. This example fixes a direction for one relation key.
Other keys can define simulation, cost bounds or other judgments.

Formally the checked relation relates the ordered endpoint keys when
there exists a witness accepted by an authorized verifier for the
fixed context `(theory, model, relation, interface)`. Acceptance
must be sound for that context's declared predicate. A reader may
compose refinement claims only with a shared middle endpoint in
the same context, or with checked transport, and a rule establishing
transitivity for that relation. Symmetry and reflexivity likewise
require rules. Equality evidence is reversible in its theory
congruence. Opposite refinements establish two directed judgments.
Any inference of theory equality from them requires a separate rule.
Substituting an equal endpoint in refinement requires a compatibility
result for the selected model and predicate.

### Validation and versioning

A verifier link identifies an immutable scheme, including the version
of its witness grammar and checking rules. Registry descriptors can
use the following exact tuples.

| Linked object | DASL tuple |
| --- | --- |
| Model | `["string-diagram/model/v1", scheme, parameters]` |
| Relation | `["string-diagram/relation/v1", scheme, parameters]` |
| Verifier | `["string-diagram/verifier/v1", scheme, parameters]` |

`scheme` is a nonempty string registered for that descriptor kind and
version, and `parameters` is shallow DASL validated by that scheme.
For a verifier those parameters select a witness grammar and
checking rules. A profile and signature are likewise resolved under
their declared schemas. Readers select an authorized local
implementation for the exact keys and check their compatibility.
Check exact tags and tuple arities, resolve the context and operands, check profile,
signature and interfaces, and validate the witness against those exact
keys. A failed witness is a rejected claim, not a proof of its negation.
Distinguish malformed objects and missing dependencies from an
unsupported tag, context or verifier. Only successful replay contributes
to a checked relation.

Future tags, model and relation keys, and witness grammars can coexist
in a store. An older reader may preserve an unrecognized object
opaquely and report it as unsupported, without validating a judgment
from it. A new revision of a theory or model has a new key. Transferring
an old claim requires another check or an explicit, verified transport
rule. A relational index uses `(theory, interface, lhs, rhs)` for
equality and `(theory, model, relation, interface, source, target)` for
refinement, with evidence links as witnesses. Several witnesses may
justify the same judgment. Keep the orientation in the refinement
index and treat stored claims as candidates until verification.

## Worked examples and verification

- `["string-diagram/v1",[2,2,[[1,2,"f"],[2,1,{"op":"g"}],[0,0,null]],[0,3,1],[2,4]]]`.
  Sources $0,1$ are the diagram inputs, $2,3$ are outputs of the
  first box and $4$ is the second box's output. Splitting the input
  table by `[1,2,0]` gives `[[0],[3,1],[]]`. The only box dependency
  is $0\to1$, and every source is used once. With source types
  $[X,Z,U,V,W]$, the required generator shapes are $X\to UV$,
  $VZ\to W$ and $I\to I$. The boundary is $XZ\to UW$.
  In destination order the quads are `(-1,0,0,0)`, `(0,1,1,0)`,
  `(-1,1,1,1)`, `(0,0,-1,0)`, and `(1,0,-1,1)`. The box
  hypergraph has tail and head lists `([0],[2,3])`, `([3,1],[4])`,
  and `([],[])`, with left and right legs `[0,1]` and `[2,4]`.
  The nullary box stays in the header and contributes no quads.
  The exact open hypergraph is

  ```json
  ["open-directed-hypergraph/v1",
    ["directed-hypergraph/v1", [null, null, null, null, null],
      [[[0], [2,3], "f"], [[3,1], [4], {"op":"g"}], [[], [], null]]],
    [0,1], [2,4]]
  ```

- `["open-directed-graph/v1",["directed-graph/v1",["x"],[[0,0,null],[0,0,null]]],[0,0],[]]`
  is a graph with two self-edge occurrences, two domain positions at
  vertex zero and an empty codomain. A domain index of 1 is out of
  range. This graph needs extra conditions to be read as a string
  diagram's box hypergraph.
- With two noncentral nullary generators on an empty boundary,
  interpreting them as assignments of 0 and 1 to a shared cell gives
  final states 1 and 0 in the two execution orders. Both orders have
  empty value dependency. The premonoidal order distinguishes the
  schedules.
- On a single through strand with source ordinal 0, a nullary box
  can have slice row `[0,0]` or `[0,1]`. With gap 0 the strand is
  in `R`, and with gap 1 it is in `L`. In either case both `U` and
  `V` are empty, so the export table is `[0]`. The core agrees for
  both slice rows and the placement differs.
- `["string-diagram/v1",[2,2,[],[],[0,0]]]` has use counts `[2,0]`.
  It copies input 0 and deletes input 1. This is an unrestricted
  structural wiring and fails the three narrower usage tests. Changing
  the exports to `[1,0]` yields a linear symmetric swap.
- `["string-diagram/v1",[0,0,[[1,1,"f"]],[0],[]]]` is linear but
  cyclic. It represents one box whose output feeds itself. Cutting
  the edge yields a $1\to1$ diagram on which trace is applied. The
  empty diagram with one standalone loop instead uses the extension
  with `loops = [null]`. A cycle test on box dependencies alone
  cannot see that component.

[Lean definitions](../Silmaril/Formats/Dasl/StringDiagram/Defs.lean)
and the [shallow codec](../Silmaril/Formats/Dasl/StringDiagram/Wire/Defs.lean)
cover core structural validation and encode/decode recovery.
The [input-group theorems](../Silmaril/Formats/Dasl/StringDiagram/Thms.lean)
prove both directions of regrouping for arbitrary entries, including
zero-width groups. The [examples](../Silmaril/Formats/Dasl/StringDiagram/Examples.lean)
exercise the codec with opaque labels and malformed inputs.

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Dasl.StringDiagram.Examples'
```

The graph and claim tuples, evidence replay, remaining layout inverses,
and categorical claims above are specified at the document level.
