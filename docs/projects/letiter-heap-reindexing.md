# Reindexing LetIter heap traces

The index arrows are typed equivalences, with identity, composition and inverse
from `Equiv`. `Reindex.indexHom` identifies them with arrows in Mathlib's core
groupoid of types. The automorphism group at `I` is `Equiv.Perm I`. A finite
index set, a structure and a subtype of strings can serve as representations of
the same indices when explicit bijections connect them. Function transport
precomposes with the inverse on the domain and postcomposes with the forward
map on the codomain. Relation and list-language transport pull observations
back along the inverse.

## Heap dialect

`Heap.instructions` instantiates native LetIter's `InstructionModel` with the
existing reply-indexed weak interaction trees. The ordinary LetIter evaluator
exposes each primitive as a typed request. The handler admits exchanges
according to the partial store `I → Option (PUnit ⊕ I)`.

| LetIter instruction | Result | Successful exchange |
| --- | --- | --- |
| `alloc(initial)` | Reference | Choose any index whose lookup is `none` and initialize that cell with `initial`. |
| `get(index)` | Value | Return the value of a live cell and preserve the store. |
| `set(index, newValue)` | Unit | Replace the value of a live cell. The LetIter operand is a product in index-then-value order. |
| `free(index)` | Unit | Remove a live cell and make its index eligible for later allocation. |

A full store admits no allocation reply. Access to an absent index admits no
read, write or free reply. References inside stored values can outlive the cells
they name. The value sum keeps the fixed unit payload separate from the
reference case, which transports along with store keys, request operands and
replies.

## Checked observation and reuse

An admitted observation is an existing `ITree.Trace` together with a
relational replay of its completed exchanges. The trace can stop at an
uninspected prefix, a pending request or a return. A pending request remains
observable when the handler has no admissible reply. The observation records no
separate fault or deadlock marker. The underlying weak tree treats finite
`tau` as the identity.

`SignatureEquiv.tree` transports coherent finite tree observations, using the
inverse reply map to select each source continuation. Its identity and
composition laws are checked. `SignatureEquiv.replay_iff` lifts any two-way
handler step law to finite replay. For the heap, `fresh_iff` transports the live
domain test and `step_equivariant` covers all four primitives.
`trace_equivariant` compares membership after transporting the tree, initial
store and observation. `trace_image` identifies the entire transported
language. For a permutation fixing the program denotation and store,
`trace_fixed_iff` gives invariance of that program's language.

The regression checks a closed native LetIter term with allocation, write and
read. It stores and reads a self-reference. It verifies that the same term's
denotations are related by tree transport, including a swap on `Fin 2` and a
change of carrier to `Bool`. It also checks finite exhaustion, visibility of
the pending allocation, and allocation after freeing a cell. The general trace
theorem takes a tree as input. Naturality of the native evaluator for every
typing derivation, including its iteration operation, is outside this result.
The observations are finite and the development supplies no infinite-trace,
eutt or concurrency theorem.

## Further models

In nominal terminology the automorphisms act on representations of states,
requests and observations. A nominal-set model would additionally specify an
atom supply and prove finite support. See [Nominal Sets](https://doi.org/10.1017/CBO9781139084673).
The checked identity and composition
laws give the transport expected of a groupoid action. A language extension can
reuse the handler theorem by proving the two-way step law for its primitives.
A concurrent model would also need equivariant scheduler, shared-state and
observation rules. The tree destructor law is the corresponding compatibility
with one layer of the observation coalgebra.

An injection into a larger carrier can support a one-way simulation when each
source step is reproduced inside the image. The target can also allocate
outside the image, and a full source store can have a non-full target. A
possible extension uses Kripke-style worlds of partial bijections on live
indices, extended when a pair of fresh indices is chosen. It would need its
own simulation and observation theorems.

For an institution whose sentences assert trace properties, the trace-image
theorem supplies the membership calculation behind the satisfaction condition
`M' ⊨ Sen(e)(φ) ↔ Mod(e)(M') ⊨ φ`. This would also require choices of
sentences, models, reindexing functors and satisfaction. See the existing
[institution facade](logic-inst.md) and
[Goguen and Burstall](https://doi.org/10.1145/147508.147524).

Run the focused regression with
`lake build --wfail +Silmaril.Proofs.SSA.Isotope.LetIter.Heap.Regression`.
