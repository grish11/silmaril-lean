# Compose capture identification and insertion

For the pure guarded five-block loop, `Composition.thenMap first second`
composes two sort-preserving port maps. `reduct_thenMap` reads a final typed
valuation in the opposite order. `reduct_embedding` also accepts the insertion
and permutation paths from `ContextEmbedding`. All comparisons use the resulting
old valuation, where any identified old ports necessarily have the same value.
[Typed maps and laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/Composition/Thms.lean)

Given an admitted program, these are the two compiler calls.

- `Composition.compileStaged first insertPath admitted` checks the identification,
  runs the original FIFO checker at the intermediate signature, then runs the
  embedding compiler at the final signature.
- `Identification.compile (Composition.thenMap first insertPath.portMap) admitted`
  transports the original program directly and checks at the final signature.
  Both calls emit the existing guarded MLIR CF and numbered RVSDG artifacts.

`program_thenMap` composes transport of the ordered writes and their operands,
both routing ports, and the return port. `checkWrites_embedding` proves that
adding an embedding preserves the Boolean singleton-preimage check on every
written destination. `pushFacts_thenMap` equates the concrete covered sets of
the staged and direct intersections for any two typed maps. A refused
intersection has empty coverage. A fresh slot in an insertion is unconstrained
and ignored by the reduct.
[Embedding API](rice-loop-sccp-context-embedding.md) · [Identification API](rice-loop-sccp-capture-identification.md)

`compileStaged_checker_iff` locates a staged FIFO refusal precisely. The
intermediate write check and fact intersection must both pass, and admission of
those exact quads and facts must reject. The example exercises `neitherMarked`
when contraction lets analysis prove an immediate exit, separately from
`incompatibleFacts` for conflicting constants. The comparison API requires
success of each call independently.

`Composition.compare` runs both paths and retains their success evidence.
For a returned `Compared`, `native_run` relates every source budget to the
original at the reduced input. `coverage_iff` compares the actual final
contracts, including fallback entries. `returns_iff` and `noReturn_iff` compare
exact returns and their absence with independent witnesses for MLIR CF,
numbered RVSDG and linked coloured Petri. A Petri witness is a finite completed
trace. `Compared.satisfaction_iff` compares the existing equation and
termination sentences across compiler paths. Both paths agree with the
native partial-word observer on the reduct image. An equation compares
partial words including equality when both are undefined. Termination
requires a finite return.

## Run both paths

The preheader adds two distinct read-only `i8` captures. The identification
makes the addition read a shared slot twice. Insertion puts an unused `i16`
between the two predicate ports. The printed triples are native, emitted CF,
and emitted numbered RVSDG, each at its own budget.

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Example
  (staged direct compared refusal run)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Example
  (conflicting changesAdmission)

#eval compared.isOk
-- true
#eval (run staged 0 true, run direct 65535 true)
-- (some (some 99, some 99, some 99), some (some 99, some 99, some 99))
#eval (run staged 65535 false, run direct 0 false)
-- (some (some 14, some 14, some 14), some (some 14, some 14, some 14))

#eval refusal conflicting
#eval refusal changesAdmission
```

[Checked example and regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/Composition/Regression.lean)
