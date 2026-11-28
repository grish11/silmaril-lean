# Packed execution of normalized φ-SSA

## Finite returns

A finite return of the predecessor-indexed source semantics is equivalent to
finite evaluation of the accepted Isotope elaboration. The translation first
uses the checked φ lowering and then elaborates its exact lexical CFG with
`NamedFlat.elaborate`. Each positional capture must agree with the source
input at the corresponding lexical name. Both evaluators use the same tagged
values and the same stateless partial primitive implementation. The explicit
`none` return label is the only external label, so its exit index is zero.
[φ lowering](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/Thms.lean) · [Finite bridge](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Thms.lean) · [Named lexical correspondence](https://github.com/hiloopai/silmaril-lean/pull/3396)

The packed theorem additionally requires exact typing of the closed graph and
a capture-closure witness for the accepted elaboration. The capture producer
must evaluate to exactly the original capture record with unchanged state.
The packed evaluator reports a tagged return at its single exit. The named
adapter checks the supplied typing profile and restricts the supported
primitive syntax. [Capture closure](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Capture/Thms.lean)

The regression exposes the numeric countdown through a typed sum-producing
classifier and closes four captures. The packed evaluator observes the
backedge swap of `2` and `5`, including the latch's ordinary live-in, and
rejects the sequential-assignment result. The mutable correspondence also
applies to the intermediate tuple-argument CFG produced by `Phi.lower`.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Examples.lean) · [Mutable correspondence](https://github.com/hiloopai/silmaril-lean/pull/3415)

Normalized φ inputs require one edge per source-target pair. [φ interface](lambdassa-theorem-crosswalk.md#conventional-φ-nodes-and-block-arguments)

## Atomic infinite paths

A source infinite path starts with a successful entry and continues with a
successful internal transfer at every index. The local correspondence reflects
each successful lexical entry and continuation to a source transfer with the
same encoded packet. The lifted path retains the predecessor and store for
the next φ assignment. [Local transfer theorems](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/Infinite/Thms.lean)

The same accepted elaboration, shared stateless partial primitives, capture
agreement, exact packed typing and state-preserving capture packet give an
equivalence with atomic packed divergence. The repeating classifier in the
typed regression takes the backedge and keeps swapping unequal values. The
stuck classifier fails before the first internal successor. Both source
runners return `Part.none`, and only the repeating classifier gives a source
path or packed divergence. [Infinite bridge](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Infinite/Thms.lean) · [Named atomic divergence](https://github.com/hiloopai/silmaril-lean/pull/3443)

## Global SSA admission

The optional certificate gives a finite set of names available on arrival at
each named block, before its φ destinations are defined. The entry starts
with the declared inputs. The checker reads each ordinary operand before
its instruction's definitions and checks each case arm with its own payload
binder. A φ operand is read at the selected predecessor's terminator. Each
internal route must justify its successor's arrival claims. [Checker](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/WellFormed/Defs.lean)

A passing certificate proves unique static definitions, including declared
inputs and binders in unreachable blocks. Every read on every syntactic
entry path has an earlier definition or a declared input. This covers
same-block order and dominance across blocks. The certificate must cover
every reachable target. It can omit unreachable blocks, and weak arrival
claims can cause rejection. The regressions admit a loop-carried operand and
reject a sibling branch's payload on the wrong φ edge, a same-block forward
read, and a duplicate static definition. [Soundness](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/WellFormed/Thms.lean) · [Regressions](../../Silmaril/Proofs/SSA/LambdaRTL/CFG/Cyclic/Phi/WellFormed/Examples.lean)

`GlobalSSA.compile` adds that source guarantee to the result of
`Phi.compile`. The original compiler and its entry, transfer, and run
theorems still require only the structural φ admission and their stated
model assumptions. Primitive and value typing, typed Isotope admission,
and capture agreement are separate obligations. [Source semantics](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/Thms.lean) · [Typed admission](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Thms.lean)

## Visible interaction trees

`NamedFlat.Phi.runTree` runs the original predecessor-indexed evaluator in
the shared weak ITree model. It evaluates every selected φ operand against
the predecessor's outgoing store and commits the φ assignments in parallel before the
target body runs. The lexical packet encoding commutes with entry and the
continuation of every step, including stores reached after primitive replies.
Weak-tree iteration lifts those equations to the whole run. [Local and whole-run equations](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/ITree/Thms.lean)

The open bridge uses the actual accepted elaboration with matching entry
captures. The packed bridge also requires exact closed typing, a
capture-closure witness, and a capture expression that runs the supplied
producer and packs the capture environment for each reply. Both use the
same primitive trees. The external list is `[none]`, so an explicit return
occupies slot zero and receives the corresponding packed tag.
[Named elaboration](https://github.com/hiloopai/silmaril-lean/pull/3473) · [Effectful capture closure](https://github.com/hiloopai/silmaril-lean/pull/3495)

The bridge accepts the original structural lowering equation. The regression
supplies it through `GlobalSSA.compile_sound`, and uses `compileTyped` and
`Capture.close` for the checked target. The producer's reply supplies the
first tick operand. A continuing tick reply is bound on the self-edge and
becomes the next request's operand through the φ node. Either tick can
return through the packed exit. The equation is in weak ITrees. The finite
and infinite atomic results above are stated in `Part`.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/ITree/Examples.lean)

## Checked admission and closure

`Certified.admit` runs the global SSA checker and the typed elaborator in
sequence. The source witness establishes normalization, definition uniqueness
and use availability. The target witness supplies its exact elaboration and
typing at the given capture, block and return profiles. An admitted result can
run `admitted.close` with a closed expression of the packed capture type.
Successful closure supplies the closed graph's typing and its erasure relation
to that same admitted graph. [Checked results](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Defs.lean)

The end-to-end theorems consume the result of closure. They recover the
lowering, elaboration, typing and closure premises from the returned evidence.
The positional capture environment is derived from the source store and
the selected version-zero names. The remaining semantic premise is that the
capture expression produces exactly this record. In weak ITrees it runs the
supplied producer, then packs the source store for each reply. In the atomic
`Part` theorems it returns the record with unchanged state. In each case both
sides use the same primitive implementation.
[End-to-end theorems](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Thms.lean)

The visible backedge regression uses these checked outputs directly. A wrong
Isotope return type rejects the same graph with its valid source certificate.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/ITree/Examples.lean)

## Canonical pure capture

`Certified.PureCapture.close` takes the existing admission and synthesizes
its closed packet expression. The target signature adds an input read for
each finite capture slot, with the slot's type from the admitted profile.
The generated expression supplies unit to each read and assembles the same
newest-on-the-right product as `packedInputType`. The original graph's
operations retain their signatures and interpretations. [Generator](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Defs.lean)

The slot interpreter reads the existing version-zero projection of the
source store. The packet proofs yield exactly `Capture.packEnv` of that
projection, with no visible event and unchanged atomic state. This is an
agreement about the supplied tagged values. Static slot typing comes from
the profile. The execution theorems take the successful pure closure,
the source store and the shared primitives, and cover weak trees, finite
atomic returns and atomic infinite paths. Custom effectful producers use the
explicit packet contract above. [Pure endpoint](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Thms.lean)

The visible regression starts with a tick under pure capture and uses its
reply as the next tick operand. The atomic regression selects two distinct
inputs in reversed positional order and returns them in source order.
[Visible regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/ITree/Examples.lean) · [Atomic regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Examples.lean)

## Finite trace comparison

Two independently admitted and purely closed graphs can be compared at
matching typed interfaces. `InterfaceMatch` requires the same positional
capture types and the same type at the sole external exit. `MatchedInputs`
pairs the source stores and requires equal projected version-zero values at
each slot. The comparison shares the event family and tagged runtime values.
Each graph can use its own primitives, with the same implementation on its
source and packed sides. The interface witness relates static slots and
projected values. Any runtime typing invariant is a separate premise of a
client that needs it. [Interface](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Defs.lean)

`packed_pointwise_traceLE_iff` transports finite trace inclusion in both
directions over any family of matched inputs. Source observations run the
predecessor-indexed evaluator and use the same exit number and return tag
as the packed dispatcher. Requests and their typed replies pass through
unchanged. The proof uses the checked pure execution equality for each graph.
The result compares executions with supplied primitive interpretations.
[Transport](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Thms.lean)

The regression certifies, admits and closes two graphs independently.
Every seed gives inclusion from the partial tick graph to the total tick
graph. At seed `4`, replies `2` and `0` each pass through the self-edge's φ
operand to the next visit. Only the total graph requests `tick 0`, which
witnesses strict inclusion for the packed executions.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Examples.lean)

## Block-local simulation

`Local.Simulation` gives a sufficient rule for the trace comparison. Supply
a relation on pending transfers at aligned block boundaries and a relation
on the local body trees and their reply continuations. At a paired jump,
`Local.step_jump` exposes the actual predecessor lookup and parallel φ
assignment. It reads every operand in the outgoing store and passes the
updated store to the block body. This is where a client can establish its
live-register and runtime value invariants. Typed admission and matching
external profiles are required when transporting the result to packing.
[Local witness](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Defs.lean)

A local match must find the same indexed request and relate the continuations
for every reply, or find the same encoded exit. Paired internal transfers
return to the boundary relation. An unpaired left transfer must take an
actual step before consulting the relation again. Each match may follow
finitely many silent internal transfers on the right. The proof inducts
over the finite left normalization prefix and the finite trace, so even an
infinite silent loop needs no global termination premise. An observable
left prefix always requires a finite match on the right.
[Soundness](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Thms.lean)

The cyclic fixture checks separate admissions for renamed registers and
headers. The right entry passes through a silent block with its own typed
profile. At each header the selected operands must be the same numeric
value. A continuing reply writes it to the backedge operand on both sides.
The local proof yields inclusion for the actual pure packed dispatchers
at every seed.
[Fixture](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Examples.lean)

## Checked edge splitting

A split plan supplies a register equivalence, a block-label embedding, a
destination, an entry or named predecessor, and a fresh forwarding label
outside the embedding's image. The self-edge plan remains the default.
The rewrite redirects just the chosen predecessor–destination pair and
inserts a block with no φ rows or register writes. It places the new block
at the old predecessor's row position, before the renamed predecessor
or at the front for an entry edge. The affected φ column changes key
and every other key undergoes only label renaming.
[Syntax and checker](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/Split/Defs.lean)

The checker requires both graphs to be normalized and the candidate to equal
the computed rewrite of an existing internal edge. A predecessor means
either the unnamed entry or one named block. Two branches from one
predecessor to the same internal destination fail normalization, including
branches in different case arms. An explicit return has no destination
block. The checker splits the sole branch for the chosen pair.
[Normalization](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/Defs.lean)

A checked result constructs both block-local simulations. The split side
follows one extra silent transfer with the same renamed predecessor store.
The row theorem preserves each operand under register renaming. The
assignment proof evaluates all operands on the fixed pre-assignment
snapshot. Both directions use the shared primitive interpretation and
preserve visible requests and replies, so trace inclusion in both directions
gives equality of the weak trees.
[Row theorem](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/Split/Thms.lean)
· [Packed endpoint](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Thms.lean)

Packed equality uses independent certified admissions and pure closures.
The typed alignment requires identical positional capture types and sole
exit type, and each target capture name must be the renamed source name at
the same position. The input store is transported by the register
equivalence. Internal block profiles are checked independently, including
the new forwarding block's profile.

The packed regression splits a distinct latch's backedge. The latch's old
column precedes an unaffected named predecessor in table order and keeps
that position. The unaffected predecessor supplies `tick 2 5`. After a
continuing reply the split backedge supplies `tick 5 2` through simultaneous
assignment. Other checks cover an entry split and reject a stale key and
parallel branches. The fixtures supply any version-zero slots required by
the cyclic versioner's packet layout in both capture profiles.
[Fixtures](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Examples.lean)

## Generating split admissions

`Split.generate` starts with the original typed admission, its finite
arrival certificate, and the split plan. The admission retains a
well-formedness proof. The caller supplies the old arrival table because the
proof alone does not retain that executable data. The generated certificate
renames the old claims. When the original destination has a claim, the new
forwarding block claims both those names and the free reads of the selected
φ column. The selected predecessor had to supply both at the original edge.
An omitted destination claim leaves the forwarding block outside the
certificate too. The existing target checker verifies the arrival claims
and global SSA definition uniqueness. The declared SSA inputs are only renamed.
[Generator](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Admission/Defs.lean)

The versioner computes a common register support from syntactic free reads.
Moving the chosen φ column can make a formerly local operand free in the
forwarding block. The lexical entry can then require its version-zero
value for the common packet, even before the source evaluator uses that
register. Generation reads the old packet-cell types from the admitted
block profiles and recovers the moved operand types from the destination's
φ payload. It rebuilds the block packets in the actual split support order,
using a unit φ payload for the forwarding block. It appends missing
version-zero capture slots without moving or changing the original slots.
The new slots read the same source store through the register equivalence.

Every returned result has passed target normalization, global SSA,
elaboration, exact typing and pure closure. The capture embedding proves
type and store-projection agreement for all original positions.
`Generated.packed_eq` uses the generated pure closure and the original
pure closure with a shared primitive interpretation. It permits the two
packed capture records to have different lengths.
[Capture and execution theorems](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Admission/Thms.lean)

Generation is partial. It needs a decodable original packet profile and
compatible types in the generated register packets. Existing capture slots
keep their types, even if the original entry ignored them. The regression
shows that plain capture renaming can fail elaboration and that an unused
original capture with the wrong type for a new read causes generation to
reject. From just the two seed captures, generation adds the two required
slots and proves the visible packed swap. The distinct latch fixture
reuses all original slots and the entry-edge fixture also generates a closure.
[Regressions](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Examples.lean)

### Success conditions and failure stages

The arrival transport theorem starts from an accepted original table, an
existing selected edge, the plan's fresh label, and successful normalization
of the rewritten graph. Renaming preserves static definitions and the scan
of every unchanged route. For the selected route, its old terminal scan
establishes both the moved φ reads and the destination claim. The reconstructed
forwarding claim carries both, so the selected predecessor and the
forwarding route each pass. This applies to entry edges and named
backedges, including unvisited blocks that have claims. An accepted
original table under these hypotheses rules out an arrival diagnostic.
[Arrival transport](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Admission/Thms.lean)

Once profile reconstruction produces a candidate, `generate_eq_of_profile`
reduces success to exact named elaboration and typing at that candidate
profile, followed by pure closure. This retains the actual checker for
the reconstructed packet types, including types of the moved operands.
The original finite table is still an input because `Admission` retains
its soundness proof. The entry and backedge fixtures use this theorem
with generated profiles and evaluate the remaining checks.

`generateDetailed` reports the stage that rejected the split. In
particular, an arrival failure reports a failed reconstructed table.
An old-capture-types failure reports the positions of retained slots
whose type changes make the same elaborated graph and block profiles
pass the exact type checker. The accepted interface keeps those types
fixed. Other typing failures retain their own stage, since the suggested
slot changes might be insufficient. The fixtures distinguish a missing
arrival table from a newly live old slot with an incompatible type and
derive the target closures for both packed swap traces.
[Diagnostics](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Admission/Defs.lean)
· [Fixtures](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Examples.lean)

## Comparisons at a supplied typed entry record

The [admitted named entry institution](https://github.com/hiloopai/silmaril-lean/pull/3717)
can consume the actual checked elaboration retained by a normalized φ
admission. The translation selects distinct version-zero names at the
supplied record positions. The private `none` name, if selected, has
unit type, as required by the φ input store. The sole external exit is
the explicit return `none`, numbered zero, with a common payload type.

`Admitted.observe_toSSA` and `Admitted.observe_toFlat` identify the weak
trees at each supplied typed record. The source evaluates its φ rows
independently. The target uses the admitted lexical table and existing
entry packer. Both use the raw primitive trees of the same typed
institution model, whose compatibility field relates those trees to the
typed instruction interpretation. The comparison preserves and reflects
satisfaction in the named room for a common named interface, and in the
flat entry and packed rooms when the two sides use different register
or label types but share the typed record and exit profile.
[Translation and satisfaction](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/Thms.lean)

`Admitted.ofGenerated` reuses the generated target admission, including
its transported arrival proof. It requires an empty list of extra
capture slots, so renaming leaves the supplied record type fixed.
`split_observe_eq` and `split_satisfies` give pointwise tree equality and
both directions of the admitted comparison. The distinct-latch fixture
uses the same supplied record to see `tick 2 5` followed by `tick 5 2`
after a continuing reply, including in the packed institution's
translated program.
[Split corollaries](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/Split/Thms.lean)
· [Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Examples.lean)

### Splits that append capture fields

The generated target keeps its larger typed entry context.
`Admitted.ofExtended` reuses its actual admission after checking that the
target names are distinct and that any private `none` slot has unit type.
`retainedRecord` pulls a supplied large record back to the original
context along the checked slot embedding. That reindexing preserves the
input decoder's value at every retained slot.

The minimal additional data to extend a given original input are
values of the appended field types. The typing and arrival certificates
specify these types without supplying inhabitants. The comparison
takes a larger record and relates it to its projection. It uses the
larger record's store, pulled back along the register equivalence, for
both independent φ runs. The original admission shows that the run
depends only on the retained slots. Both the older `Generated.packed_eq`
and the projected comparison use the same generated source-observation
equality.
[Record reindexing](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/ITree/Entry/Record/Thms.lean)

`split_named_reindex` and `split_packed_reindex` give pointwise weak tree
equality at the related records, with the same singleton return type.
`split_related_satisfies` gives both directions of trace inclusion in
the named and packed observations. The generated self-edge fixture
starts from the two seed fields and supplies distinct nonzero values
for the two appended fields. It checks both directions and observes
`tick 2 5` followed by `tick 5 2` through the packed program.
[Split comparison](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/Split/Extended/Thms.lean)
· [Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Examples.lean)

### Composing generated splits

`Record.reindex_id` preserves a supplied record, and
`Record.reindex_comp` reindexes along the composite slot map by
projecting successively from the final context back to the original
one. Both operations read fields already supplied in the input record.

`EntryComparison.ofSplit` packages the checked slot map and the
observation equality of a generated split. `EntryComparison.comp`
requires the exact same admitted table at the shared endpoint.
`EntryComparison.satisfies_iff` pulls predicates on the admitted named
and packed observations back along the composed projection at each
supplied final record. This covers either direction of pointwise
trace inclusion by fixing the other observation. The final record
supplies the typed values for all appended fields.
[Composition and satisfaction](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/Split/Comparison/Thms.lean)

The cyclic fixture splits the swap backedge, adding two capture fields,
then splits the entry edge into the renamed header. The second generator
uses the first generated admission and the checked transported arrival
table. It retains the four-field context. The fixture projects the final
record to the original two seeds, checks trace inclusion in both
directions, and preserves `tick 2 5`, a continuing reply, then
`tick 5 2` in both evaluators.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Examples.lean)

### Relabelling primitive instructions

Primitive relabelling acts on the block bodies. It preserves predecessor
keys, φ operands, normalization, and the result of checking the same
arrival table. The checked φ lowering and cyclic versioning commute with
the opcode map. `Admitted.map` transports existing well-formedness and
the ordinary named typed-entry certificate at its exact capture, block,
and exit profiles. Generation still runs at the original signature and
produces the split admissions and pure closure used by that route.
Relabelling those admissions consumes their stored evidence. Running
generation again at a different signature would check a new result.
[Graph and arrival transport](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/InstructionMap/Thms.lean)

`EntryComparison.map` keeps the checked slot projection and transports
the admitted endpoints. Mapping before or after composing the comparisons
gives the same result, including the shared admitted table. At every
supplied final record, pointwise comparisons of the named and packed trees
agree with the original comparisons in the existing typed-entry model
reduct. The signature map preserves primitive input and output types and
the bottom effect. The event family and reply types are shared.
[Comparison and reduct](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/InstructionMap/Thms.lean)

The two-split fixture identifies the distinct `tick` and `finish`
opcodes. After the continuing reply and the simultaneous swap, the
second tick replies with `11`. The finishing primitive requests
`tick 11 11` and its typed reply `23` supplies the old payload in both
relabelled evaluators.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Examples.lean)

### Checked reverse lowering to mutable RTL

The φ entry bridge passes the actual admitted flat table to the
[packet-local reverse checker](https://github.com/hiloopai/silmaril-lean/pull/3818).
The reverse runner reads the same typed input slots in the same order,
under supplied RTL register names. Its sole declared exit occupies
position zero, matching the numbered φ return.

The reverse interface expects the explicit return operand
`(old payload, ordered live-out record)`. The flat branch must write a
pair, with a unit record for an empty live-out list. The reverse checker
also checks packet locality and exact readback after attaching the RTL
live-out reads. This detects a field-order mismatch even when the
affected fields have the same type. The original checker supports
straight-line lets, supported operands, and jumps.
[Typed case support](https://github.com/hiloopai/silmaril-lean/pull/3867)
adds scoped sum terminators with jumps or nested cases in each arm.

`Admitted.observe_reverse` composes the independent predecessor-snapshot
observation theorem with equality for the emitted mutable RTL run and
its projected final store. `Admitted.observe_reverse_roundTrip` also
uses a successful ordinary re-admission of that RTL, at its supplied
internal packet types.
[Bridge](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/Reverse/Thms.lean)

The fixture runs two φ blocks and swaps `7` and `9` across the second
edge. Both the emitted RTL and its actual admitted reversion request
`tick 9 7` and return the reply with ordered live-outs `9, 7`.
Reversing the selected fields is rejected by exact readback.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/Reverse/Swap.lean)

The admitted polling fixture uses the typed case support on a genuine
self-edge. Its continuing branch sends both swapped values together in
one packet. On the supplied seeds, the independent predecessor-snapshot
runner requests `tick 2 5`, takes a continuing reply, then requests
`tick 5 2`. A later reply `11` starts the finishing request
`tick 11 11`, whose reply `23` returns as the old payload with live-outs
`5, 2`. The actual reverse checker and ordinary typed re-admission
both accept the polling table. The emitted mutable body retains the
self-edge, and both the emitted and re-admitted observations contain
the complete request/reply trace and return at exit zero.
[Cyclic regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Examples.lean)

### Ordered external exits

The ordered admission takes a list of distinct external labels disjoint
from the internal block table. The checker requires each written branch
to target a block or a declared exit. The existing φ arrival checker
analyzes the graph with declared exits identified for scope analysis,
which preserves their payload reads and the internal predecessor rows.

The independent runner keeps the written label and payload on an
external branch. On an internal branch it evaluates the selected φ
operands in the predecessor snapshot. The lowerer uses the existing
packet decoder and cyclic versioner. `Admission.observe_packed`
relates the source observation to the actual typed table at the declared
exit order. After accepted reverse readback, `Admission.observe_reverse`
relates it to the emitted mutable RTL with its projected final store.
Successful typed re-admission yields `Admission.observe_roundTrip`.
Each exit supplies its own old-payload type and ordered live-out record.
The φ admission uses a supplied block profile. The numbered regression
uses the existing reverse re-admission and its
[packet-profile synthesis](https://github.com/hiloopai/silmaril-lean/pull/3897).
[Ordered admission and agreement](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Thms.lean)

The regression branches on a typed sum after a φ swap. Each arm returns
the same old payload `13` and live-outs `(9, 7)`, using different
physical registers for the two exit records. The right exit is declared
first and the left second. The emitted and re-admitted runs
preserve the distinct tags even though their payload records are equal.
The checks reject an omitted exit and a reversal of the live-out reads
at just one exit.
[Two-exit regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Examples.lean)

### Splitting before ordered reverse lowering

`checkSplit` checks the existing single-edge rewrite against the two ordered
graphs. The selected destination must be a block, even when a declared exit
has a written incoming branch. Each ordered admission still checks the exit
partition, normalized predecessor rows, scope certificate and types. The
forwarding hop keeps the predecessor store, and the rekeyed φ column reads
the same operands from that snapshot. An internal branch argument is ignored
at block entry. External labels and payloads remain observable.

`Admission.split_reverse_eq` compares the actual mutable graphs emitted by
the two successful reverse checks. `Admission.split_roundTrip_eq` compares
the actual packed programs after successful typed re-admissions. Both
theorems use a common input record and live-out profile. The source capture
names follow the plan's register equivalence, and the plan fixes the exit
list positionally. The theorems require separate accepted typed admissions,
reverse checks, and (for the packed comparison) typed re-admissions.
[Checked semantic square](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Split/Thms.lean)

The two-exit regression also splits the internal edge that carries the
crosswise copy. It generates the forwarding arrival claim with the existing
split helper. Both paths use a common five-slot record with two older typed
slots for the captures required by the split. Both reverse outputs and both
re-admitted tables return the same ordered live-outs at the selected exit.
[Split regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Examples.lean)

#### Generating the ordered split admission

`Admission.generateSplit` takes the admitted original and a split plan.
It constructs the split graph and the renamed static inputs and arrival
table. Collapsing the declared exits for scope checking commutes with the
internal split, so the existing arrival transport applies. The generator
checks the target's exit partition and predecessor rows, then reconstructs
the packet profile in the ordered lowering's actual block and register
orders. It runs the ordinary typed compiler on the original record layout
with renamed capture names. A candidate with missing capture slots is
reported by `Admission.splitProfile` and fails fixed-record generation.
The candidate supplies names and types. The input record supplies values.
[Generated admission](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Split/Admission/Defs.lean)

The swap requires two older numeric slots because the new forwarding
packet carries the moved φ operands `y` and `x`. The original admits
without these slots, while the generated target's actual typed elaborator
rejects either omission and a mistyped slot. Both operands are assigned
before traversing the edge. The emitted RTL and re-admitted results hold
for every pair of older numeric values supplied in the common record.
The generated scope table adds the two names to the forwarding arrival
claim, while the list of static SSA inputs stays the same.
[Generated swap regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Examples.lean)

The generator can also reject packet reconstruction or typing at retained
slots. The execution corollaries consume the existing reverse readback
and ordinary typed re-admission results. The source-local versioner has
its own saved-record checks.
[Execution corollaries](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Split/Admission/Thms.lean)

#### Liveness of the moved operand captures

`Admission.movedCaptureSlots` selects the retained slots reported by
the reconstructed profile. Each such name was absent from the original
lowering's register support. The original lexical entry therefore has
no free read of it at version zero. The original versioned blocks read
only their incoming packets, so agreement at the entry's free capture
slots gives equality of the entire weak observation tree, including
request replies and ordered exits.

`GeneratedSplit.observe_eq_of_movedCaptures` transports this criterion
through the checked split. Two records at the same admitted interface may
differ at every reported slot if their other fields agree. The split's
actual typed packed execution and, after the respective checks, the emitted
RTL and typed re-admitted execution have the same observation on both
records. This is a sufficient liveness criterion. The generator still
requires and checks the field types, and the two records supply their own
values.
[Capture liveness](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Split/CaptureLiveness/Thms.lean)

The swap fixture checks that the generated lexical entry really reads
both older slots and that the original entry reads neither. It then
compares the actual emitted and re-admitted runs while varying both
numeric fields together, for each branch of the original exit choice.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Examples.lean)

#### Source-local re-admission of the two reverse outputs

`GeneratedSplit.roundTrip_eq_of_uniformReadback` constructs both typed
re-admissions with `Straight.admitWithCaptures`. It takes the actual checked
reverse outputs at the same numbered interface. Each graph has its own
saved slot list in the versioner's packet order, a check that the attached
bodies leave those registers unassigned, and source-local checks at the
original packet types. These conditions produce the scoped readback and
typed compiled tables used by the ordered split comparison.
[Composition theorem](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Split/UniformReadback/Thms.lean)

The swap's original table saves `[1, 2, 0]` at every internal destination.
Its split table saves `[1, 2, 4, 3, 0]`. Both reserve a separate register
for the incoming block parameter. Starting from the supplied record, the
mutable entry and each successful internal step preserve the saved fields.
The packet check uses that store agreement explicitly, so it preserves the
supplied values and their tags in the actual destination order. The
constructed re-admissions retain the two ordered exits and the checked
independence from the older slot values.
[Swap checks](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Examples.lean)

#### What remains of reverse acceptance after emission

`GeneratedSplit.reverseChecked_iff_readback` identifies the remaining
condition once the ordinary reverse lowerer has emitted an RTL table.
Emission fixes the block count. Successful scoped readback implies packet
closure because each block is elaborated with only its own parameter in
scope. The readback must equal the generated split's flat table with the
declared live-out reads attached. The ordered φ admission supplies the
typed flat table and its profiles. Acceptance uses the supplied reverse
allocation and checks the exact ordered live-out readback.
[Reverse acceptance theorem](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Split/ReverseAcceptance/Thms.lean)

The swap fixture constructs the split's reverse certificate using only
successful emission and its exact readback equation. It also checks two
rejections. Reusing the original accepted allocation fails after the
split. With the relocated allocation, exchanging the two numeric
left-exit registers still emits a scoped, packet-closed RTL table that
elaborates and typechecks at the generated profile. Its final flat block
differs from the admitted one, so exact reverse acceptance rejects it.
[Swap regressions](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Examples.lean)

#### Inferring the relocated reverse allocation

`GeneratedSplit.reverseRelocated` starts with the original checked reverse
allocation and its actual RTL output. It reads the generated split's flat
table with the existing reverse body lowerer, using symbolic names for
inputs, the block parameter, and each local binder depth. Keeping the exit
arguments in that pass reveals the binder required for each declared
live-out position. The solver preserves the original physical exit names
and packet parameter. For unrequested depths it chooses distinct names
above the original writes and the requested registers.
[Inference](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Split/Relocation/Defs.lean)

The supported fragment uses numbered input registers, direct variable
reads in the ordered live-out record, and one allocation for each local
depth throughout a graph. The same depth must satisfy every request for
it. Forced names at distinct depths must be distinct and outside the
entry captures and the packet parameter. Reads of an input or the packet
parameter require their fixed physical name. The inferred allocation
satisfies these constraints, and the ordinary reverse checker still
verifies the actual emission and its exact flat readback.
[Soundness](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Split/Relocation/Thms.lean)

The swap now obtains its allocation from this inference. The four
live-out requests pin depths `12, 14, 16, 17` to registers
`14, 16, 18, 19` in exit-record order. The existing same-typed
swapped allocation fails the requests and still produces the exact
readback counterexample.
[Swap regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Examples.lean)

#### When graph-wide relocation succeeds

After the symbolic pass has extracted the ordered direct reads, there is a
valid allocation exactly when the fixed packet parameter lies outside the
numbered captures, all requested local names avoid the captures and the
parameter, and the requests form a partial bijection. A depth must request
one name across all bodies. Each requested name must belong to one depth.
Repeating the same request is allowed. Unrequested depths can always be
assigned above the finite set of original writes and requested names.
The deterministic allocator succeeds exactly under these conditions.
[Allocation theorem](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Split/Relocation/Thms.lean)

A checked branching split exposes the global restriction. One arm exits
directly from the entry and the other traverses the selected φ edge before
exiting. The split adds one saved field, moving the latter exit's binder
from depth six to eight. The entry at depth eight requires physical
register 14, while the destination block at the same depth requires
register 12. Each body's list is satisfiable separately. The single
graph-wide allocation cannot meet both requests.
[Branching regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Examples.lean)

Allocation and reverse acceptance have separate success criteria. After
emission at the inferred allocation, acceptance requires exact readback.
The swap's valid allocation still emits when every internal label is
assigned the same name, but exact readback rejects that label map.

#### Opt-in body-local reverse allocation

`GeneratedSplit.reverseRelocatedByBody` uses the same numbered capture
registers and packet parameter throughout the emitted RTL. It solves the
ordered direct-read requests separately for the entry and each internal
body, then runs the ordinary reverse emission and exact readback checks
with those allocations. It also checks injectivity of the combined
internal and external label map. The existing reverse entry points keep
the graph-wide allocation policy.
[Body-local allocation and acceptance](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Split/Relocation/Local/Thms.lean)

The branching split allocates depth eight to register 14 in the entry and
register 12 in its exit block. Readback recovers the actual typed split
table, including both declared ordered live-out records. The attached
RTL is packet-closed. At a fixed label and packet, its next observable
transfer is independent of the carried mutable store. The store still
travels with transfers. Re-admission carries the checked capture fields,
which are separate from body locals and the packet parameter and agree
with the supplied record through successful internal steps.

Both branching tables re-admit via the uniform-capture constructor. The
packed regression observes exit 1 with payload and live-out 13 on the
direct arm, and exit 0 with payload and live-out 7 on the arm that crosses
the new forwarding block. Both internal label collisions and collisions
with declared exits are rejected.
[Branching regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Examples.lean)

#### Whole-run agreement for exact body-local reverse readback

`Admission.bodyLocal_commutes` takes a checked ordered φ admission and a
successful `lowerCheckedWith`. At one supplied typed input record and under
one compatible primitive model, it identifies the actual `lowerWith` output
and equates its attached mutable RTL run with the independent φ runner and
the encoded result of typed packed LambdaSSA denotation. The common weak
tree retains visible requests and replies, the declared exit index, and its
payload followed by the ordered live-out fields. The φ evaluator reads each
row from the predecessor snapshot. Exact readback recovers the flat table
and its packet interfaces. `Admission.observe_recompiled_denote` also covers
the packed program obtained by successful typed re-admission of that RTL.
[Whole-run theorems](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/Execution/Thms.lean)

The cyclic proof lifts packet-closed step agreement through Elgot iteration
without a rank bound. At a resumed transfer, `Lowered.resumeAttached_eq`
erases carried-store differences at a fixed label and packet.
`Lowered.resumeSaved_eq` compares that continuation with the actual
versioned dispatcher. It uses the checked destination slot layout and
agreement of the carried store with the supplied record on those slots.
The branching fixture derives this agreement at reached transfers from
the saved-capture invariant.
[Continuation theorems](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/ITree/Entry/Reverse/Execution/Thms.lean)

The polling regression uses different entry and block allocations and keeps
an actual self-edge. Its trace requests `tick 2 5`, `tick 5 2` after the
continuing reply, then `tick 11 11`. The later reply returns 23 with live-outs
5 and 2 in that order. The generated-split corollary retains the separate
check on the combined internal and exit labels.
[Polling regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Examples.lean)

#### Directed handled-trace verdict at a matched public entry

`PublicMatch` connects an ordered φ admission and its checked reverse output
and typed re-admission to an existing finite public `PackedEntry`. It uses
the same typed input record on the φ and RTL side. At the specified public
packet it requires capture agreement and a weak-tree equation for the
re-admitted packed program, after the common result encoding. The primitive
model shares the public event signature, including each request's reply
type, and carries typed-to-erased primitive compatibility. The two public
programs share the declared input and output profiles.

For two such witnesses, `refinementAt?_iff_source` uses the existing
all-replies verdict to decide directed satisfaction for every shared handler
at that packet. A handler uses the same initial-state predicate and replay
relation on both sides. The source, attached RTL and checked packed
executions satisfy the same directed judgment under each policy. When the
result encoding is injective, the verdict also reflects finite trace order
on the original φ results. The witness supplies semantic alignment with the
finite checker at this packet. It leaves construction of finite public
programs for general φ graphs open.
[Bridge](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/HandledTrace/Thms.lean)

The regression aligns two checked graphs at the same unit input and visible
request. After the reply one graph enters a self-edge that carries a φ
operand and the other returns at exit 1. The existing verdict accepts in the
loop-to-return direction and rejects the reverse. The actual attached RTL
also replays the ordered return through a handler that moves from its
initial state on the reply.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/HandledTrace/Examples.lean)

#### Constructing the public observation from exact readback

`PublicMatch.ofReadback` derives the whole-run equation from the flat
table recovered by exact reverse readback and the actual checked public
entry. The round-trip theorem connects that table to the re-admitted
LambdaSSA program. On the φ side the typed input record supplies
`Entry.inputEnv`. On the public side the record must agree with the
public packet at the capture names selected by `PackedEntry`. Both
dispatchers use the existing packed context decoder.

`Readback.Alignment` compares the resulting entry transfer and each
local block step at their decoded captures. Its state codec translates
private block indices and packets. The result codec maps only the atomic
carrier and preserves the ordered exit and the shape and ordering of its
fields. Both primitive interpreters use the same event family, and the
step equations compare all reply continuations. Elgot iteration then
lifts the local equations across cycles. Exact readback identifies the
φ table and exact public elaboration identifies the comparison table.
The local alignment premises relate those two tables.
[Readback bridge](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/HandledTrace/Readback/Thms.lean)

The fixture compares the actual admitted flat rows to their public
elaboration and proves the local packet equations. Its φ entry builds a
packet containing one φ argument and a saved capture. The matched public
entry reads that literal packet from its capture slot. One variant passes
the primitive reply around a self-edge and the other returns it at exit 1.
The whole-interface result applies after covering the sole public entry
and the only inhabitant of its structural packet type. The two accepted
tables also witness that exact acceptance alone cannot align the looping
readback with the returning public dispatcher.
[Readback regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/HandledTrace/Readback/Examples.lean)

#### Deriving the local equations from matching erased rows

`Readback.Provenance` ties the local endpoints to checked code. Exact
reverse readback identifies the φ-side flat table. The public
`PackedEntry` identifies its table by accepted elaboration of
`Program.compile`. At each position the two erased bodies must equal
one flat row scoped to its incoming packet. The witness retains block
and exit order, and the state codec keeps the positional block index.
Shared packet scope lets the two ambient capture records differ at
unused slots.

For the entry, the φ readback is a jump whose structural argument comes
from its capture slots. The public entry's accepted elaboration determines
the jump and the positional slot for the public packet. Record agreement
identifies the value in that slot with the public packet's typed encoding.
The entry equation uses equality of that encoding with the encoded source
packet. For a row, the codec commutes with the erased evaluator under the
explicit primitive agreement, including every reply and malformed erased
arguments. The output map preserves the positional exit tag and the product
and sum structure of the return.
[Local provenance and equations](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/HandledTrace/Readback/Provenance/Thms.lean)

The cyclic fixture now compiles the actual public row at packet scope and
checks its erasure against both accepted tables. The generic constructor
discharges the local equations for both variants and feeds the existing
coverage proof. This fragment requires a structural entry jump and exact
row correspondence. Constructing a public dispatcher from other φ readbacks
requires additional compilation, such as splitting a row that has several
primitive continuations into the public checker's one-application rows.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/HandledTrace/Readback/Examples.lean)

#### Constructing the public dispatcher from the ordered readback

`Admission.constructPublic` starts with the admitted table and its exact
reverse readback. It recovers the structural expression carried by the
entry jump and takes the public packet type from the destination block.
It translates the admitted packet and live-out profiles to the finite
structural codec, keeping source block indices and the declared exit order.

The indexed traversal builds typed `Visible.Code` rows. It uses the
existing public compiler, named elaborator, and type checker to check the
actual emitted public table. It then reconstructs both erased rows at
packet-only scope and compares them. Successful construction carries the
row elaboration equations, exact public typing, and the erasure evidence
used by `Readback.Provenance.alignment`. Capture and primitive agreement
remain separate execution premises.
[Construction API](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/HandledTrace/Readback/Construction/Ordered/Defs.lean)

The generated fixture has two blocks in nonnumeric label order, with
different φ packet types. The visible reply drives the second row, whose
two paths return to distinct ordered exits with different payload types.
The independent source observation agrees with the generated packed
program at the fixture's supplied capture packet.

The public row grammar supports product unpacking before pure branches,
or one primitive followed by a literal jump. The regression checks a
well-typed flat row with two consecutive primitive requests and shows
that it falls outside that grammar. Atomic base types in the packet or
exit profiles require a separate finite codec.
[Generated regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Entry/OrderedExits/HandledTrace/Readback/Construction/Examples.lean)
