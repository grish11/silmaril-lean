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
`tick 11 11` and its typed reply `23` is the returned payload in both
relabelled evaluators.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Split/Examples.lean)
