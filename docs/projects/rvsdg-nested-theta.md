# Compositional θ regions

`Silmaril.SSA.RVSDG.NestedTheta` adds θ as an ordinary typed vertex in any
region, including a γ arm or another θ body. Reissmann, Meyer, Bahmann and
Själander specify θ in *RVSDG: An Intermediate Representation for Optimizing
Compilers*, arXiv:1912.05036v2, §4.1.3 and Definition 3. The versioned PDF
has SHA-256 `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2)

The inductive term binds a sequence of typed vertices. The graph has a
numbered vertex table, child-region table and result wires. Each child has
an empty local prefix. A θ has one body, identical outer input and output
signatures, and body results `.control 2 :: carried`. A true body predicate
feeds its updated tuple to a fresh activation. A false predicate publishes
that tuple on the outer output ports. The graph's local edges remain acyclic.
Round trips preserve each representation exactly at its given numbering.
The primitive/γ and whole-region θ embeddings preserve the old observations.
[Definitions](../../Silmaril/SSA/RVSDG/NestedTheta/Defs.lean) ·
[Theorems](../../Silmaril/SSA/RVSDG/NestedTheta/Thms.lean)

## Operational correspondence

`Term.Exec` specifies finite return independently of fuel. A let reads its
typed sources and binds the node's result before continuing. A γ derives
a return only from the selected arm. A θ return is an inductive
`Theta.Iterate` derivation with a finite series of complete body returns,
ending with a false predicate.

`Graph.run` executes the numbered vertex table directly. A bound of `n`
permits up to `n` body activations at each θ invocation, including the final
one. Every nested invocation receives the same bound independently. This
is a per-invocation bound, so multiple siblings and nested iterations can
execute more than `n` bodies in total. For every output,
`Graph.returns_iff` relates a successful run at some bound to the
unbounded term derivation. Every finite derivation yields a sufficient
bound that succeeds at all larger bounds.

A failed bounded run can lack fuel at an outer or inner θ. Failure at every
bound means no finite return derivation in this model. The current theorem
does not classify that case by infinite executions. In particular, a
nested body may lack a return even when there is no infinite sequence of
completed iterations of the outer loop.

The fixture builds the root graph directly. A γ arm contains a θ, and a
later θ consumes the γ state output through an ordinary wire. Its body
contains another θ. The test exercises both selectors and different
sufficient iteration bounds.
[Fixture](../../tests/ssa/RVSDGNestedTheta.lean)

## Categorical and Petri hooks

The categorical θ constructor can use the existing selector coproduct at
`K₂ ⊗ X`. Route port zero's zero tag to the return summand and its one tag
to the feedback summand of `X ⨿ X`, then apply Elgot iteration in the
computation category. `Kind.Exec` supplies the finite-return criterion
for an adequacy theorem with a specified categorical observation. Its
body relation is at the carried interface, with ambient wires captured
by the surrounding binder. The primitive/γ denotation can retain its
existing domain.

For the next firing proof, define a nested `Step` with a waiting control
cell carrying exactly the selected γ marking or the active θ body marking.
A completed true θ body discards its cells and installs a fresh body
marking from the updated tuple. Define `Finishes` by finite reachability
and prove, for each well-typed numbered region and input/output tuple,

```text
NestedPetri.Finishes m g input output ↔ g.Returns m input output
```

For soundness, maintain completed vertex return derivations and, at each
waiting θ, a finite prefix of continuing body derivations. Completing a
child then either extends that prefix or gives a `Theta.Iterate` witness
ending in a stop. For completeness, recurse on the finite term execution,
lift selected child steps into the parent cell, and use the local numbering
to construct a schedule ready at every required source. The target theorem
quantifies over all finite completed schedules. Infinite firing behavior
and progress of arbitrary partial markings require separate statements.

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.NestedTheta.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedTheta.lean
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.NestedTheta.Thms
```
