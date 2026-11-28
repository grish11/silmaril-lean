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

## Native evaluator naturality

`LetIter.Reindex.typeEquiv` extends a family of base-carrier equivalences
through products, sums, unit and empty. `freeEnvEquiv` maps the values of
visible free names at their declared types, and `boundEnvEquiv` transports
each bound slot. Extending a bound valuation commutes with this transport.

`LetIter.Reindex.denote_natural` compares direct monadic evaluation of the
same native typing derivation in two set interpretations into weak ITrees.
The event signatures can differ. The required primitive law says that
evaluating a primitive at the transported operand gives the transported
tree, with the return value mapped at the declared result type.

`SignatureEquiv.tree_bind` transports sequencing when the continuations
agree at corresponding inputs. `SignatureEquiv.tree_iter` transports both
feedback and exit values. Its proof works at every finite observation
depth, where `Part` iteration resolves silent feedback and the induction
hypothesis handles the next visible layer. It applies to arbitrary loop
bodies, including silently divergent ones. These two laws let the proof
recurse over all native syntax, including case, abort and iteration.

For structured calls, the signature equivalence keeps the primitive symbol,
transports its operand and reply at their declared types, and commutes with
the evaluator's universe lifting. The resulting primitive square discharges
the hypothesis for all four heap instructions. `Heap.denote_natural` and
`Heap.denoteClosed_natural` give native heap evaluator naturality.

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

`Heap.denote_trace_equivariant` compares finite trace membership for native
open terms after transporting the valuation, store and observation.
`Heap.denoteClosed_trace_image` gives the whole target language for closed
terms and any transported initial store. An empty store is fixed by every
pointer permutation, so `Heap.denoteClosed_trace_rename_iff` gives invariance
for each closed term started in the empty store. All results use the weak
tree and finite handled observations.

The regression keeps the allocation, read, write, exhaustion, pending request
and reuse-after-free checks. A second closed native term reads a stored
self-reference as iteration feedback, frees that pointer on the next step,
and returns it. The checked trace renames the allocation reply, request
operands, read reply and final result. The examples check both a swap on
`Fin 2` and transport from `Fin 2` to `Bool`.

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

Run the regression with the pinned Lake toolchain.

```sh
make check CHECK_TARGETS=+Silmaril.Proofs.SSA.Isotope.LetIter.Heap.Regression
```
