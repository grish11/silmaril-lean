# Handled interaction-tree institution

The signatures are typed interaction-tree event families. An arrow (f : S 	o T)
sends a packed source request (q) to a target request (f(q)). Its second field
sends each reply to (f(q)) back to a reply to (q). Neither field requires an
inverse. Composition runs the request maps in arrow order and the reply maps in
reverse order. `Signature.sum`, `Signature.inl`, `Signature.inr` and
`Signature.desc` let a client combine event families and interpret each summand.
`Signature.ofEquiv_tree` identifies this translation with the existing
`SignatureEquiv.tree` for invertible changes of notation.

## Sentences and models

A sentence consists of a weak ITree, its result type and a predicate on results.
`Sentence.translate` translates the tree and its continuations, leaving the result
type and predicate in place. A model specifies a state type, an initial-state
predicate and a relational handler. For an arrow (S 	o T), `Model.reduct`
keeps the target state and initial predicate. A source reply is legal for a
transition exactly when the target can make that transition with a reply that
maps back to the source reply. In particular, a reduct can have several legal
successor states for the same source reply.

The model categories are discrete. Their arrows are just equalities of model
data, including the state type, initial predicate and step relation. The
identity and composition laws use equality of relations and reassociate the
existential witnesses. This institution makes no choice of simulation or
refinement arrows between handlers. An explicit state equivalence instead
transports initial states and steps through `Model.renameState`, with identity,
composition and reduct commutation checked separately.

`Sat` requires the postcondition on every handled finite return from every
initial state. `runs_iff_handledTrace` identifies the indexed run relation with
the existing `HandledTrace` observations ending in a return after the given
number of exchanges. `runs_translate` transports such runs in both directions.
`sentences`, `models` and `satisfaction` assemble the library's
`ClassicInstitution`. The checked laws are partial-correctness laws. They
allow a program with no admitted return and do not classify stuck requests,
faults, or divergence. Concurrent scheduling is outside this profile.

## Heap, read-only view and clock

The heap model uses the typed events and the actual `Heap.step` handler from
[LetIter heap reindexing](letiter-heap-reindexing.md). The read-only signature
keeps queries but omits allocation, mutation and freeing. The functors
`heapSignatures` and `readSignatures` map the existing typed location groupoid
into effect signatures. `readInclusions` is natural. For (e : I simeq J),
`translate_readInclusion` compares the two forward sentence translations
from read-only (I) to heap (J). `heapModel_reduct` and `readModel_reduct`
compare the backward reducts to the source models whose stores have been
renamed forward by `storeEquiv e`. `heap_sat_rename` gives the induced
satisfaction equivalence.

- `lifecycle_sat` checks that any admitted return after allocation, a
  self-reference write, a read, and a free carries the allocated reference.
  `lifecycle_runs` witnesses a completed run from the empty store for every
  possible allocated location. `lifecycle_denote` identifies the program with
  the checked native LetIter denotation, using the existing small-reply
  representation. `lifecycle_finTwo_to_bool` checks the law across a change of
  location type.
- `readLaw_sat` checks that two successful reads of the same cell agree from
  every heap state. `readLaw_swap` translates that sentence into the full heap
  and swaps locations 0 and 1.
- `optionalTick_sum` translates an optional-reply clock into a Boolean-reply
  clock and then into the heap-plus-clock sum. The backward reply map is
  `some`, so the translated run cannot produce `none`. The clock increments
  its own state and preserves the heap. `optionalTick_sum_runs` witnesses a
  successful tick in that combined model.

Use the pinned toolchain to build the public headers and Lean regressions.

```sh
lake build --wfail \
  +Silmaril.Proofs.SSA.Isotope.LetIter.Heap.Institution.Regression \
  +Silmaril.Proofs.SSA.Isotope.LetIter.Heap.Institution.Clock
```
