# Factor a typed guarded SCCP capture map

Supply a sort-preserving `Identification.PortMap S T`. The compiler profile
has a fixed pure five-block quad program, primitive interpretation and result
width. The map can identify read-only captures and leave target slots unused.

- `Factorization.compressed map` computes the used target bank in target
  order. `compress map` maps every old port into that bank, and
  `embedding map` reinserts the omitted positions using the existing typed
  weakening and permutation API. Compression is surjective at each sort,
  and the embedding hits exactly the used ports. `thenMap_eq` recovers the
  supplied map. `reduct_factor` pulls valuations back through the factors
  in reverse order.
- `checkWrites_compress` gives exactly the same singleton-preimage check as
  the supplied map. A written destination cannot alias another old port.
- `liftChecked map oldInput fill` returns a final valuation precisely when
  every pair of old ports mapped to the same target port agrees. It takes the
  first old representative of each used target port and preserves the
  caller's `fill` at every unused port. `reduct_image_iff` characterizes the
  image independently of the fill, `liftChecked_sound` proves the lifted
  target reduces to the requested input, and `liftChecked_none_iff`
  characterizes refusal.

[Port and compilation API](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/Factorization/Thms.lean) ·
[Checked lift and image laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/Factorization/Ports/Thms.lean)

Call `Factorization.compileStaged map admitted` to check the compact
bank and replay the embedding, or `Identification.compile map admitted` to
check and emit directly. `Factorization.compare map admitted` uses the
existing comparison API to obtain both artifacts and their success evidence.
A successful comparison implies actual one-shot compilation of the supplied
map by `direct_compiled`. The intermediate and direct FIFO checks each
require admission. A valuation lift only checks image membership. The
artifacts still evaluate their entry guards, and an accepted lift can take
the fallback arm.

`staged_coverage_at_lift` and `staged_returns_at_lift` compare original
coverage and exact finite returns at a lifted old input. The shared
comparison also gives native block-budget agreement, direct returns and
absence, and separate finite witnesses for CF, numbered RVSDG and linked
coloured Petri. Petri absence is absence of a finite completed trace.
`staged_satisfaction_at_lift` and `direct_satisfaction_at_lift` use the
existing equation and termination sentences. Both undefined partial words
satisfy an equation between them. Termination requires a finite return.
[Staged compiler and observation laws](rice-loop-sccp-port-composition.md)

## Run the example

The two `i8` operands of the preheader addition map to the same target
register. Slot 1 is an unused `i16` between two used predicates. The outputs
of `run` are the staged and direct results, each ordered as MLIR CF and
numbered RVSDG.

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Example
  (keptSlots liftedGap compared run)

#eval keptSlots
-- [0, 2, 3, 4]
#eval (liftedGap 7 65535, liftedGap 7 0, liftedGap 8 0)
-- (some 65535, some 0, none)
#eval compared.isSome
-- true
#eval (run 65535 true, run 0 false)
-- (some ((some 99, some 99), (some 99, some 99)),
--  some ((some 14, some 14), (some 14, some 14)))
```

The refused lift sets the two identified old inputs to 7 and 8. The
regression proves there is no final valuation with that reduct.
[Checked regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/Factorization/Regression.lean)
