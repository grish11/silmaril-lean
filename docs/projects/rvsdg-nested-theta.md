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

## Categorical interpretation

The Kleisli interpretation keeps entry and producer tuples in the Cartesian
value category of types. Pure wires can project, duplicate and discard these
values, including state snapshots. A let reads the typed wires, runs the node
once, and passes the retained scope and appended result to its continuation.
Each child opens a fresh scope on its entry tuple. Primitives are the pure
images of the total operations of a runtime model. The selector and payload
form the finite coproduct of one payload type per tag, so a γ uses the
Kleisli copair by indexing the arm with the tag. The branch's computation
runs before the continuation. [Definitions](../../Silmaril/SSA/RVSDG/NestedTheta/Categorical/Defs.lean)

A θ first computes its recursively interpreted body, then sends tag zero
to the left return summand and tag one to the right feedback summand. The
chosen Kleisli coproduct is compared to the ordinary sum before applying
the repository's iteration operator. `iterate_stepArrow` identifies this
categorical iteration with the operation in the fold. The fold takes a
lawful monad on types with an iteration operation, and the Elgot laws apply
when the monad supplies them. The categorical interpretation of a numbered
graph uses its typed table decoder, so the syntactic round trip proves
agreement with the term arrow at fixed numbering. The Elgot conventions use
Ghalayini and Krishnaswami, *The Denotational Semantics of SSA* (2024),
arXiv:2411.09347v1, §§5.1 and 5.3. The versioned PDF SHA-256 is
`5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
[Theorems](../../Silmaril/SSA/RVSDG/NestedTheta/Categorical/Thms.lean) · [PDF](https://arxiv.org/pdf/2411.09347v1)

In deterministic `Part`, membership in the denotation is equivalent to
`Term.Exec`, including at an open binding prefix. The proof uses `Part`'s
finite iteration derivation for each θ, relates its stop and restart
premises to complete child derivations, and composes the node and its
continuation by the membership rule for bind. The result applies without a
nesting limit. A graph's partial return is exactly the output of its typed
decoder's unbounded derivation and thus of its direct evaluator at some
sufficient fuel. The fixture checks finite returns through nested θ and γ,
including a successful selection with an unselected arm that has no finite
return. Selecting that arm instead yields `Part.none`.

`Part.none` characterizes the absence of any finite return. A single fuel
failure leaves open whether greater fuel succeeds. An infinite sequence of
completed outer iterations also cannot account for an inner call with no
return. A general infinite-execution characterization, a general
premonoidal adapter, and a nested-region institution remain separate from
these adequacy theorems.

The [nested firing semantics](rvsdg-nested-petri.md) proves the
finite-completion equivalence against the unbounded term relation. It
uses explicit child activations and fresh θ re-entry, including under γ.

## Ordered state

The same fold accepts a computation arrow for each primitive. Its existing
pure entry points embed the total value primitives with `pure`. The ordered
instance uses the structured runtime's `Instruction P E` dialect and lifts
each `StateM σ` primitive into `StateT σ Part`. The typed ports carry values,
selectors, and unit state slots. The live state stays in the computation, so
reading or copying an in-scope port cannot recover a previous runtime.
[Definitions](../../Silmaril/SSA/RVSDG/NestedTheta/OrderedState/Defs.lean) · [Primitive lift](rvsdg-structured-runtime-lift.md)

The independent `OrderedState.exec` relation records a finite derivation in
dependency and binding order. Each node receives the state left by its
predecessor. A γ passes it to the selected arm in a fresh value scope, and
each θ restart receives the carried tuple and state returned by the completed
body. Sequencing therefore fixes an order for the effects without a
commutation assumption. `mem_denoteOpen` proves equivalence with membership
in the stateful denotation at every prefix. `mem_observe` applies this to
the typed graph decoder. Both observations identify the entire result tuple
and final state together. [Theorems](../../Silmaril/SSA/RVSDG/NestedTheta/OrderedState/Thms.lean)

The fixture has a θ inside another θ. The inner θ advances state twice per
outer activation. The next outer node reads that state to choose whether to
restart and to determine the returned payload. Choosing the uncharged γ arm
returns payload 7 and state 15. Choosing the arm that adds 100 returns
payload 102 and state 205. [Ordered fixture](../../tests/ssa/RVSDGNestedThetaOrderedState.lean)

## Explicit runtime wires

`ExplicitRuntime.Checked` admits nested terms over the structured runtime
opcode dialect. It extends the flat live-wire rules. Every region enters with
one runtime at the last port. Each binding uses only its designated live
origin and its continuation can use only the token returned by that binding.
The data signatures of instructions and regions exclude runtime ports. The
selected γ arm gets the incoming token at its own boundary. A θ enters its
body with the carried tuple and token. Each completed body routes its updated
tuple and token together to the next activation or to the exit.
[Admission and erasure](../../Silmaril/SSA/RVSDG/NestedTheta/ExplicitRuntime/Defs.lean)

Erasure retains the numbered port positions. Runtime slots in the erased
value scope are unit, and the erased instructions use the same ordered
`StateM` actions as the explicit ones. `Checked.exec_iff` compares the two
unbounded finite relations at an arbitrary admitted prefix. The live wire
determines the implicit starting state. A boundary comparison pairs the
erased output tuple with the final token, and the proof uses a bijection at
each data-only interface. `observe_eq_some` composes this result with
`StateT σ Part` adequacy for the erased graph and with the finite-return
theorem for the explicit graph evaluator. Both directions concern the
entire result and final token. The theorem is for supplied admission
witnesses and finite observations in this deterministic model.
[Theorems](../../Silmaril/SSA/RVSDG/NestedTheta/ExplicitRuntime/Thms.lean)

The state fixture also assembles and checks explicit versions of the two
γ arms and the nested θ body. Both branch results agree with the implicit
observations, including payload 7 and token 15 when the arm that adds 100 is
skipped. [Fixture](../../tests/ssa/RVSDGNestedThetaOrderedState.lean)

The partial-primitive bridge extends these observations to exact blocked
attempts and productive divergence. [Partial explicit wires](rvsdg-nested-partial-wires.md)

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.NestedTheta.Categorical.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedTheta.lean
lake build --wfail +Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedThetaOrderedState.lean
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Thms
lake env leanchecker Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Thms
```

The [interprocedural graph interfaces](rvsdg-interprocedural.md) use these
regions for function bodies.
