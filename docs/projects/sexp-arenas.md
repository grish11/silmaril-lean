# Binary S-expression arenas

Import `Silmaril.Formats.SExp.Arena.Thms` and open
`Silmaril.Formats.SExpArena`. Expressions are the library's
[`Silmaril.Formats.SExp2`](../../Silmaril/Formats/SExp/Basic.lean), with
atoms, `nil`, and ordered pairs.

## Storage and observations

[`Defs.lean`](../../Silmaril/Formats/SExp/Arena/Defs.lean) reads each encoding
through `Arena Ix Atom`, a function `Ix → Option (Cell Ix Atom)`.

| Storage | Adapter |
| --- | --- |
| `Ix → Cell Ix Atom` or `Ix → (Cons Ix ⊕ Atom)` | `Arena.ofMap` |
| `List (Cell Nat Atom)` or `List (Cons Nat ⊕ Atom)` | `Arena.ofList` |
| Maps or lists with `Option` or `Undef` entries | The same adapters via `CellEncoding` |
| Partial map with a finite cover of occupied indices | `FiniteLookup.normalize` followed by `.lookup` |
| Optional or undefined whole arena | `Arena.ofOption` or `Arena.ofUndef` applied after decoding |

In the sum encoding, the left lane holds a pair of indices and the right lane
holds an atom. The `Cell` encoding additionally has an explicit `nil` cell,
which denotes the empty S-expression. An undefined entry, an absent list index,
or an absent whole arena gives a missing lookup. `FiniteLookup.ofList` uses
the list's bounds as its finite cover, including any holes within those bounds.

`Arena.Unfolds` relates one index to a finite expression. Both children of
each ordered pair must unfold, and shared nodes appear once per occurrence
in the resulting expression. The relation is deterministic. The set of
expressions at a pointed arena is a singleton if it unfolds and empty if it
fails. Dangling and cyclic roots can therefore be equivalent. The
`Pointed` setoid equates precisely the pointed arenas with equal observations.

`Arena.denotation` takes the union over all indices. `Arena.exportDenotation`
takes the union over the listed roots. `Exported` is the list-root instance
of `Rooted`. Custom descriptors implement `Root.indices` and coerce to
`List Ix`. The `Rooted` setoid equates equal export denotations, discarding
order and multiplicity. `Pointed.toExports` preserves and reflects equivalence.

## Collection and reindexing

[`Thms.lean`](../../Silmaril/Formats/SExp/Arena/Thms.lean) proves that agreement
on all source-reachable lookups preserves unfolding in both directions and
preserves export equivalence. Reachability includes each export itself and
follows edges even to missing cells, so the agreement also preserves failed
lookups.

`Arena.restrict` sweeps a supplied decidable mask. `Arena.markSweep` uses
classical reachability for the mask, and `FiniteLookup.markSweep` also
filters the finite key cover. These definitions specify collection. Computing
the reachability mask at runtime is outside this model. Deleting
unreachable cells can change the whole-arena denotation. The preservation
theorem compares observations at the exports.

`Arena.Reindexes` specifies the lookup correspondence for compaction
or renaming. Each reachable source lookup must agree with the lookup at the
renamed index, with both children rewritten by the same index function.
`exportDenotation_reindexes` proves that mapping exports by that function
preserves the denotation, even across different index types. The correspondence
includes missing lookups and allows arbitrary cells outside the image of the
reachable source indices. Aliasing reachable indices is allowed when their
mapped lookups agree, so the theorem needs no injectivity assumption.

## Reference counts and cycles

`RefCounted` stores a natural-number count beside every occupied cell.
`FiniteLookup.withRefCounts` computes the counts, and erasing those counts
recovers the original finite lookup. Each car or cdr edge contributes one
incoming reference, including both edges when the two children coincide.
Counts measure internal edges. External exports retain their own list of
root occurrences. `CountsCorrect` checks the counts at occupied targets.
After deleting cells, counts can be recomputed from the swept storage.

A cycle is a nonempty child path from an index back to itself.
`Arena.CyclicBelow` asks whether such a cycle is reachable from a selected
root. A successful unfolding excludes every cycle reachable from that root.
`FiniteLookup.exists_unfolds_iff` characterizes successful unfolding in
finite storage by acyclicity below the root and an occupied lookup at every
reachable index, including the root. Infinite acyclic lookups can still
require infinite unfolding. The examples include a self-loop with a correct
positive count, a reachable hole preserved by sweeping, and recomputed counts
after deleting a cons that referenced the same child twice.

Build the definitions, theorem headers, and examples on the repository's
pinned toolchain with:

```sh
lake build --wfail +Silmaril.Formats.SExp.Arena.Examples
```

The [checked examples](../../Silmaril/Formats/SExp/Arena/Examples.lean)
also exercise encoding inference, custom root coercion, and the distinction
between export preservation and whole-arena preservation.
