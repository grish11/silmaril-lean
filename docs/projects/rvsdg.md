# Regionalized value state dependence graphs

The [standalone θ extension](rvsdg-theta.md) covers the whole-region loop and its
fresh-iteration firing semantics. The milestones below cover integrating θ as a
vertex in general RVSDG regions.

`Silmaril.SSA.RVSDG` formalizes the typed acyclic fragment with simple nodes
and multi-way γ nodes from Reissmann, Meyer, Bahmann and Själander,
*RVSDG: An Intermediate Representation for Optimizing Compilers* (2020).
The source is arXiv:1912.05036v2, §§4, 4.1.1–4.1.2, 4.3 and 5.1.3.
The versioned PDF has SHA-256
`861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2) ·
[DOI](https://doi.org/10.1145/3391902)

## Representations and theorems

[Defs](../../Silmaril/SSA/RVSDG/Defs.lean) defines two representations over
a shared typed port vocabulary.

- `Term` is inductive let syntax. A let defines an ordered tuple of outputs and
  extends lexical scope for the rest of the region.
- `Graph` stores a vertex table with local finite node IDs, a separate table of
  child graphs keyed by vertex and arm, and a tuple of result edges. A node input
  or region result is the user of exactly one edge. An origin names a typed
  argument port or an output port of a local vertex and can have any number of
  users. `Graph.producer_lt` shows that each node-to-node edge points from a
  lower-numbered producer to a higher-numbered consumer in its region.
- A primitive's indexed opcode determines its input and output types. A γ with
  `n + 2` arms receives a selector in `Fin (n + 2)` and a tuple of entry ports.
  Its arms share the entry and exit signatures, and only the selected arm runs.
  Each arm has fresh local scope and receives outside data through its arguments.
  A whole region starts with the empty prefix of local node signatures.

[Thms](../../Silmaril/SSA/RVSDG/Thms.lean) states
`Term.toTerm_toGraph` and `Graph.toGraph_toTerm`. They are inverse translations
at a fixed numbering in every region of the hierarchy. The output signatures,
wire addresses, result order and branch order are preserved exactly. The vertex
IDs give a topological order. The isomorphism result below compares different
valid numberings.

`Term.run` interprets lets in lexical order. `Graph.run` reads the graph table
directly and fires each vertex once per active region in node-number order.
`Graph.run_toTerm` and `Term.run_toGraph` give equality of returned port tuples
for every input and total deterministic primitive model. Each active region
runs all of its vertices. The observation consists of the returned tuple,
including any returned state. State sorts are distinct from value sorts, and
state sequencing is explicit through wires. Like value ports, state origins
permit fan-out and may be unused. An operation has only the effects carried
by its input and output state values in this model.

## Reproduce the checks

From the repository root with its pinned Lean toolchain:

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDG.lean
lake build --wfail +Silmaril.SSA.RVSDG.Petri.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGPetri.lean
lake build --wfail +Silmaril.SSA.RVSDG.Isomorphism.Petri.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGIsomorphism.lean
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.Isomorphism.Petri.Thms
```

The [fixture](../../tests/ssa/RVSDG.lean) constructs a graph directly as tables.
A state wire sequences a write, a three-way γ, and a read. The test checks
all three state histories, including the pass-through branch, and reads a
single value output through two result ports. It also checks an independently
constructed term and the impossibility of sourcing a value from a lone state
argument in an empty scope. For the axiom audit, import the theorem header
and use `#print axioms` on the five public theorems.

## Coloured firing semantics

[Petri.Defs](../../Silmaril/SSA/RVSDG/Petri/Defs.lean) uses typed argument and
output places, with one colour at each marked data port. A read leaves its token
in place. Each use of an origin reads the same colour, including repeated
reads by the same transition. Output tuples are published together. Each
vertex has a one-shot control token that is pending, waiting, or done.
`Graph.toTerm` enumerates the graph's ports and vertices to index the marking.
That order gives wire addresses. A firing can skip any earlier vertices whose
outputs it does not need, including vertices waiting on a child.

A primitive transition consumes its pending token, reads all its input ports
and marks its outputs and done control. A γ entry transition consumes its
pending token and creates a waiting token recording the selector and the
selected child's fresh marking. Only that child can fire under the waiting
token. Its argument colours come from the γ entry tuple. A γ commit requires
the child's completed result and retires its marking, publishing the result at
the γ output ports. A region result requires all local vertices to be done
and all its result colours to be present, even for a region with unused nodes.

`Step` relates one firing, including a firing beneath a waiting γ.
`Finishes m g input output` uses finite reflexive transitive closure from the
initial marking. [Petri.Thms](../../Silmaril/SSA/RVSDG/Petri/Thms.lean) proves
`finishes_iff`: every completed legal schedule returns `g.run m input`, and
some finite schedule reaches that result. Soundness maintains a proof
interpretation of the residual marking across **each** firing. Completeness
constructs a numbered schedule and recursively completes its selected
children. `step_unfinished` also shows that a completed marking admits no
more firings. These statements cover finite completed executions and
terminality of completed markings. Progress of arbitrary partial runs,
termination of every maximal run, and fairness are open.

The [firing fixture](../../tests/ssa/RVSDGPetri.lean) checks a complete schedule
that fires a later unused primitive first and interleaves another primitive
between two steps of a selected γ arm. The consumer reads the chosen arm's
state after commit and reads an independent value twice. The checked result
is the number `21` and state history `[1, 12, 13]`. The fixture also checks
that a pending unused vertex prevents completion and that the consumer's state
input is absent before γ commits. The axiom audit uses `#print axioms` on
`Petri.finishes_iff` and `Petri.step_unfinished`.

## Invariance under graph isomorphism

[Isomorphism.Defs](../../Silmaril/SSA/RVSDG/Isomorphism/Defs.lean) defines
`Graph.Isomorphic` by a vertex bijection in every paired region. The witness
fixes the ordered argument and result signatures and the port positions.
It preserves each vertex's input and output signatures, node shape and opcode.
It matches the source endpoint of every operand and region result after
renaming vertex IDs. Each corresponding γ arm has a recursive isomorphism
witness at the same arm position, with its own vertex bijection.

`Graph.Isomorphic.run_eq` compares the actual evaluator traces. Each vertex
reads already established colours along its incoming edges. Matched vertices
agree by induction on the left graph's numbering and by recursive agreement
of the selected arms. The right graph may use a different topological
numbering. The proof compares the inputs and outputs of corresponding
vertices, then reads the matched result wires. The [Petri bridge](../../Silmaril/SSA/RVSDG/Isomorphism/Petri/Thms.lean)
gives the same set of completed-run observations.
[Operational theorem](../../Silmaril/SSA/RVSDG/Isomorphism/Thms.lean)

The [isomorphism fixture](../../tests/ssa/RVSDGIsomorphism.lean) swaps an
independent value vertex and state vertex at the root and inside both γ
arms, preserving consumer and boundary wiring. It also checks that
redirecting a result to a different argument violates isomorphism.

## Next milestones

- **Labelled graph admission and firing transport.** Admit a labelled
  hierarchical DAG with a topological-order certificate per region and
  relate its checked presentations with `Graph.Isomorphic`. Transport
  partial markings and individual firings across the witness. The current
  Petri bridge compares only completed result reachability.
- **θ.** Thread the carried tuple through fresh activations of a body whose
  first result is the continuation predicate. Require a completed body
  before re-entry or publication. Prove finite return correspondence against
  an inductive numbered execution relation, then study divergence via
  infinite firings with an explicit observation and scheduling policy.

## Remaining RVSDG constructs and later semantics

- **λ and apply, δ, ϕ, ω (§4.2).** Add explicit capture and callable signatures
  for function bodies and calls, capture and a single initializer result for
  globals, and recursion arguments paired with definition results for mutual
  recursion. Use a single root ω region for translation-unit imports and
  exports. Add linking and call observations alongside these interfaces.
- **Denotations, translations and institutions.** First prove agreement with
  a monoidal interpretation of the acyclic operations. Extend to ordered
  effects and iteration using the existing premonoidal and Elgot interfaces.
  Specify both directions of SSA/RVSDG translation as relations on typed
  open regions and prove preservation for each related pair under a shared
  observation, including returned state and divergence where defined. A
  construction or destruction algorithm should inhabit the appropriate fibre.
  For the dialect institution, use signature-preserving opcode maps,
  relabelling of sentences and model reducts. Prove that evaluation commutes
  with reducts before packaging the satisfaction condition.
  [Existing SSA, Elgot and institution interfaces](ssa.md)
