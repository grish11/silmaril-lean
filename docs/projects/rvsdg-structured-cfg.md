# A typed grammar for structured flat CFGs

The grammar has three constructors. A leaf uses the existing typed loop
with an acyclic body. A serial link redirects two same-sort exits of one
child to the entry of the next. A branch runs a classifier, selects one
of two children, and redirects either child's exits to one shared
continuation. Both arms, the continuation, and both sides of a serial
link use the same grammar recursively. The LambdaSSA compiler emits one
actual flat `Region.cfg` by relocating typed labels at each constructor.
[Grammar and lowerer](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/Defs.lean)

The inherited branch interface uses a classifier of type
`A → (M + M) + Y`. Both left injections enter the left arm with payload
`M`. The right injection enters the right arm with payload `Y`, which may
differ from `M`. All exits feeding the join carry `M`. Final labels
may carry different types. The graph has typed serial carriers at
its boundaries. The root classifier reads the active entry injection.
A `Fin 2` selector indexes the two γ children, which each receive the
carrier and one token. The existing checked splice inserts the shared
continuation once and uses the selected child's data and exact returned
token. The connectors use the existing carrier routing and preserve
the token.

`lower` constructs a numbered graph and a syntax-directed `Related`
witness. `raise` constructs the opposite fibre from a supplied
`Decomposition` containing the grammar and exact graph equality.
The certificates are indexed by syntax and numbered wiring.
The recognizer constructs that decomposition directly from the typed
numbered graph, as described below.

## Observations

`branch_agrees` takes agreement for three independently admitted
components and uses `Flat.denote_fork` and `Flat.denote_link` to
factor the actual repository denotation. The proof compares the selected
arm with its relocated flat blocks before invoking the continuation.
The induction for all grammar trees reuses the existing serial
composition law and single-loop theorem. Primitives run in source
order in one coherent `StateT σ Part` model and may be partial.
[Agreement theorems](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/Thms.lean)

Every related pair has the same finite return, including the typed
external label, payload and exact final token. Absence of finite return
also agrees. The partial observation combines blocking and infinite
feedback. The grammar covers generated layouts with acyclic
loop bodies. Arbitrary reducible CFGs and graph renumbering remain
outside the theorem.

The regression selects an inner diamond in the left outer arm and
takes feedback in an inner loop. The outer continuation is a two-loop
serial link. The returned payload reads the token on entry to the
last loop. For input 0 the payload and final token are 123357 and
1233578. For input 3 the outer right arm skips the inner diamond,
returning 167 and 1678. For input 99 a primitive in the selected right arm is undefined, and
the checked graph has no finite return from which to start the continuation.
[Lean regression](../../Silmaril/Proofs/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/Regression.lean)

## Recover from a numbered graph

`Reverse.candidate` scans the actual outer vertex order and descends
into each γ arm. It reuses the local θ parser for loop bodies. Serial
connector opcodes identify the handoff types. The left arm's entry
connector and the two exit connectors supply the arm and continuation
interfaces, even when the two arms enter at different types.

The emitted order of serial cuts can represent several associations.
`Reverse.Normal` fixes a right-associated serial form in which a
serial link starts with one θ and a fork owns the rest of its scope
as its continuation. The parser chooses this form independently
inside each arm. The local loop parser right-associates instruction
sequences. Certification re-emits the candidate and compares the
full typed graph recursively, including selector operands, captured
arguments, results, and token origins.

`recover_isSome_iff` characterizes acceptance as literal equality with
the emitted graph of some outer normal form. It allows arbitrary sequence
association and nested acyclic choices inside those loops. When the
local bodies also use the parser's association, `recover_generated`
identifies the recovered source exactly. Other outer associations can
be accepted when their graphs coincide with the normal emission. The
regression checks this property on a three-loop serial chain emitted
with left association. A general graph equality theorem for rebracketing
all outer compositions is outside the completeness statement.

The recovered CFG has the same two observations and the same absence of
a finite return as the nested-diamond fixture. A type-correct mutation
redirects the shared tail's first token to the graph entry while retaining
the γ payload. The label parser still returns the original candidate and
certification rejects the graph.
[Reverse API](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/Reverse/Thms.lean)

## Compile through the outer normal form

`Normalization.normalize` covers every admitted structured source. It
passes a serial suffix through a preceding sequence and into a fork's
existing shared continuation. The two arm scopes stay local to the fork.
The type of the operation preserves the boundary carrier types and the
ordered vertex signature table. Applying it to a source already written
in `Reverse.Normal` returns that normal form.

`denote_normalize` proves equality of the repository's flat
`Region.denote` in the coherent monadic Elgot interface. The proof uses
the actual flat fork and flat link laws and reassociates binds. In the
partial-state model, `compile_returns_iff` and `compile_undefined_iff`
compare the original flat CFG with the newly emitted graph, including
the typed exit and exact final token. Every result of reverse recovery
on that emission has the original CFG's partial denotation.

`Normalization.compile` emits the explicit normal layout. The existing
recognizer is complete on its output for every `Syntax` witness.
`decideNumbering` uses full typed graph equality to check the earlier and
normal emissions for a particular source. The regression checks literal
equality on a fork followed by a composite suffix, where stages 8 and 9
move into the fork's continuation after stage 7. On input 0 the graph
returns payload 123357 and token 12335789. Input 99 has no finite return.
The compiler and round-trip theorem apply independently of the per-source
comparison. A universal equality theorem for the two emissions would
require a syntactic associativity law for checked splice and origin
relocation. The existing splice law gives denotational composition.
[Normalization API](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/Normalization/Thms.lean)

## Two levels of feedback

`NestedFeedback.lower` is a separate forward entry point for a flat
two-block region with an outer header of type `A`, an inner header of type
`B`, and one typed external label of type `D`. The outer block applies
`A → B` and jumps to the inner block. The inner block applies
`B → K ⊕ B` and either restarts itself or sends the completed `K` to a
`K → D ⊕ A` decision within that block. The decision exits at the external
label or restarts the outer block. The three arrows are existing typed
LambdaSSA instructions. The loop nesting is determined by this source
witness, with no general cycle recognition step.

The numbered outer θ contains the entry instruction, the inner θ, and
the final decision instruction. The inner θ receives the entry
instruction's live token, and the final decision reads both outputs of
the inner θ. Each restart uses the activation's returned token.
Coproduct carriers encode the different entry and exit payload types,
and the θ tag selects exit or restart. The shared partial instruction
model performs one source instruction per primitive. The constructor
`Related.generated` supplies the source typing and existing single-live-token
admission for the emitted graph.

`denote_rounds` derives nested iteration from actual flat
`Region.denote` in a coherent monadic Elgot model using codiagonal,
naturality and pure uniformity. In `StateT σ Part`, every relation witness
preserves and reflects finite graph returns at the typed external label,
including the exact final token. The undefinedness theorem compares
absence of a finite return. The fixture follows an inner restart in each
outer activation and an outer restart, then reads the token into the
returned payload. A second input stays in the inner loop and has no
finite derivation.
[Nested feedback API](../../Silmaril/SSA/RVSDG/LambdaSSA/NestedFeedback/Thms.lean)

`NestedFeedback.Reverse.recover` takes the typed numbered graph and
its dialect. It reads both θ regions, infers `B` and `K` from the
opcode roles, and checks the three instruction types against the
signature. It reconstructs the source and accepts only if re-emission
matches the actual graph recursively, including every typed port,
operand, child and result address. Success returns a flat region with
a relation witness indexed by that input graph. Every canonical
emission recovers its original region and both internal types.

The recovered CFG has the same finite observations and exact final
token in the coherent partial-state model. The regression reuses both
nested-feedback cases and checks a mutation that replaces the inner
θ's returned token at the decision with the outer entry token. The
mutation leaves the payload and both θ shapes intact. Parsing succeeds
and full certification rejects the differing token address. This
recognizer accepts precisely the literal numbered images of the
two-header shape. It uses the graph's outer boundary types and infers
the inner types. Other loop layouts, arbitrary renumbering, and
general CFG structuring are outside this API.
[Nested feedback reverse API](../../Silmaril/SSA/RVSDG/LambdaSSA/NestedFeedback/Reverse/Thms.lean)

## Use nested feedback as a structured leaf

`WithNestedFeedback.Syntax` adds the two-header loop at the
homogeneous join interface used by the structured compiler. Its flat
block table keeps the original local edges and exit index. The wider
type has a second external label of the same payload type. The
`Leaf.source_rounds` theorem shows every return uses the first label.

The leaf is the original checked nested θ with an entry and exit
carrier conversion. The conversions preserve the token, and the exit
conversion injects the returned payload at label zero. Links and forks
reuse the existing flat relocation, checked splice and denotation laws.
The observation theorems cover both finite returns with their exact
final token and absence of a finite return in coherent `StateT σ Part`
models.

`recoverLink` reads a supplied standalone nested graph and an existing
structured consumer graph with their local recognizers. It compares
their re-emission against the actual joint graph before returning a
typed flat CFG and relation witness.

`WithNestedFeedback.Reverse.recover` instead takes the joint graph
alone. It recognizes the entry conversion, nested θ, exit conversion
and connector prefix, taking the join and continuation carrier types
from the typed opcodes and the suffix signature from the numbered
term. It reads the structured continuation in its relocated scope.
The local decoders reconstruct both views, and one full joint
comparison checks every operand and token origin. Every nested leaf
followed by a canonical structured tail is accepted. Local sequencing
may recover in the existing right-associated form. For a tail already
in that form, recovery returns the original flat CFG. The serial
recognizer covers a leading nested leaf.
[Mixed serial reverse API](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/WithNestedFeedback/Reverse/Thms.lean)

The regression links the nested loop to an acyclic-body loop. The
consumer reads both the returned payload 1223122 and token 12231223,
then returns payload 13454345 and token 122312234. Input 99 has no
finite return and never reaches the consumer. The same observations
are checked for the CFG recovered from the joint graph alone. A
type-correct mutation keeps the exit conversion's payload but reads
the original input token at the connector. It yields the same parsed
candidate, and exact joint certification rejects it.
[Mixed structured API](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/WithNestedFeedback/Thms.lean)

## Recover a mixed fork from the joint graph

`WithNestedFeedback.Reverse.Fork.recover` covers a root binary γ
with a canonical structured left arm, one nested-feedback right arm,
and a canonical shared structured continuation. It reads the actual
classifier, the two child tables and the continuation scope. The join
and continuation carrier types come from the typed connector
opcodes. The nested arm uses the mixed serial reader with an empty
local suffix beyond its final connector. The existing structured
decoder reads the left arm and shared continuation. One full joint
re-emission comparison checks the γ operands, both arm returns and all
continuation wires. Every canonical emission of this shape is
accepted. Supported right-associated local bodies recover their
original flat CFG.

Both selected arms are checked against actual flat `Region.denote`.
The left branch yields payload 11 and token 44. The nested right
branch yields payload 13454345 and token 122312234. Input 99 selects
the nested arm and has no finite return. A stale-token variant retains
the γ payload but supplies the original input token to the shared
continuation. It parses to the same candidate and fails certification.
The scope fixes the nested leaf in one right arm at the root and
retains emitted numbering.
[Mixed fork reverse API](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/WithNestedFeedback/Reverse/Fork/Thms.lean)

## Decode canonical mixed regions recursively

`WithNestedFeedback.Reverse.Recursive.recover` reads the numbered graph
without a supplied split, child view or LambdaSSA source. The canonical
grammar has ordinary θ leaves whose acyclic bodies admit instructions,
sequences and typed choices. It also has the existing two-header
nested-feedback leaf, right-associated serial links with a
leaf on the left, and binary γ forks that own their shared suffix.
Both arm scopes and the suffix can independently use the full grammar.
The two exits feeding each serial cut or fork join have the same payload
sort. The final external labels may have different sorts.

The decoder reads typed connector opcodes and child tables, with recursion
bounded by the scanned layout. `recognize` certifies the complete re-emitted
graph once, including operands, returns, captures and the live token.
`recover_isSome_iff` characterizes exactly the literal numbered emissions
of this grammar. `recover_generated` also recovers the original flat CFG
when each ordinary loop body already uses the parser's local right
association. For any recovered CFG, the graph and actual `Region.denote`
agree on the typed exit, payload, final token and absence of finite return
in coherent `StateT σ Part` models.

The regression puts nested feedback in both arms, with an ordinary loop
before the left leaf. The shared continuation observes the returned token
from either arm. A third input selects a nonreturning nested loop. A
type-correct replacement of the continuation's token with the entry
token leaves the structural parse intact and fails certification.
The grammar uses canonical numbering, the existing nested-feedback leaf
shape and the generated `gamma 0` fork layout.
[Recursive reverse API](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/WithNestedFeedback/Reverse/Recursive/Thms.lean)

## Compile any admitted mixed source to the recursive layout

`WithNestedFeedback.Normalization.compile` normalizes arbitrary serial
association in the admitted mixed source before emitting a numbered graph.
It uses the ordinary normalizer on embedded ordinary subtrees and treats
nested feedback as an outer leaf. A suffix passes through a fork's shared
continuation once. Both arms retain the original typed join. The normalized
source has the same typed boundary and ordered signature table.

`denote_normalize` proves equality of actual flat `Region.denote` in
coherent monadic Elgot models. Its continuation law uses associativity of
ordered bind. `compile_recover` guarantees decoder acceptance and
`recover_denote` proves equality of the recovered and original partial
state denotations in coherent `StateT σ Part`. This covers either typed exit,
its payload, the exact final token and absence of finite return.

The regression starts with two left-associated links after a fork with
nested feedback in both arms. It checks that the links move into the
shared tail, then compiles and recovers from the numbered graph.
Inputs 1 and 0 return different payloads and tokens after the shared
suffix observes the selected arm's state. Input 99 has no finite return.
The equality concerns the actual source and recovered CFG denotations.
The compiler emits canonical numbering for this grammar.
[Mixed normalization API](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/WithNestedFeedback/Normalization/Thms.lean)

## Recover through a supplied typed graph isomorphism

`WithNestedFeedback.Reverse.Renumbered.recover` takes the actual
`Flat.Serial.Graph` and a representative with an indexed
`NestedTheta.Graph.Isomorphic` witness. The representative has its own
signature table. The witness checks opcodes, ordered ports, every input
and result address, and each child at its original arm or body position.
The recursive decoder computes the source from the representative and
returns a typed flat CFG with the correspondence to the actual graph.
The existing partial graph transport gives agreement with actual
`Region.denote` on the typed exit, payload, exact final token and absence
of a finite return in coherent `StateT σ Part`.
[Recovery API](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/WithNestedFeedback/Reverse/Renumbered/Thms.lean)

The current indexed graph uses topological table positions as vertex
numbers. `EntryChecked.scopeChains` shows that at every scope each
nonfirst vertex consumes the token output of its immediate predecessor.
Any address-preserving bijection into such a scope fixes every rank.
The regression recovers the compiled mixed fork with a serial tail,
checks the exact token from each selected arm and checks a path without
a finite return. It rejects a transposition at the root and in a γ arm.
It also proves that no vertex bijection can repair an entry token
substituted for the fork's output token at the shared seam. Arbitrary
external vertex IDs independent of topological positions would require
a representation carrying those IDs.
[Numbering theorems](../../Silmaril/SSA/RVSDG/NestedTheta/ExplicitRuntime/Isomorphism/Thms.lean)

## Reproduce

```sh
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization.Thms +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Regression'
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization.Thms
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Renumbered.Thms +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.NestedFeedback.Regression'
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Renumbered.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4.1.2–4.1.3. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Jad Ghalayini and Neel Krishnaswami, *The Denotational Semantics of SSA*
  (2024), arXiv:2411.09347v1, §§3 and 5.3. PDF SHA-256
  `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [Versioned PDF](https://arxiv.org/pdf/2411.09347v1)
