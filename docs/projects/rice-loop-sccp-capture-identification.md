# Identify two typed guarded SCCP captures

`ContextEmbedding.Identification.PortMap S T` gives each old typed port a
target port of the same sort. The map may send distinct ports to the same
target. `reduct` reads each target port at its old positions.
`reduct_identifies` gives equality of the old values at identified ports,
and `reduct_embedding` agrees with the existing pullback on embeddings.
All observations below compare a target entry with its pullback. Old
valuations that assign different values to identified ports are outside
that image.
[Typed map and reduct](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/Identification/Thms.lean) ·
[Injective embeddings](rice-loop-sccp-context-embedding.md)

`compile map admitted` transports each quad, operand, and terminator port,
runs the following checks, and emits the existing guarded CF and numbered
artifacts on success.

- Each written destination must be the sole old port mapped to its target
  position. `checkWrites_iff` characterizes this structural check. A
  shared slot can be read throughout the program.
- Entry facts are intersected at every target port. An overdefined fact
  imposes no constraint. Conflicting constants or a bottom fact give
  `incompatibleFacts`. A successful contract covers exactly the pullbacks
  covered by the old contract. A refused intersection has no covered
  entry in the reduct's image.
- The existing FIFO checker runs on the contracted program with the
  intersected facts. Its own refusal reason is preserved as `checker reason`.
  In particular, a contraction can establish that the header exits before
  either feedback occurrence is taken.

The typed native runner commutes with the reduct at every source block
budget. The numbered selectors choose the same coverage arm on each
corresponding input. `compile_returns_iff` compares exact words using the
existing backend witnesses, and `compile_noReturn_iff` compares absence.
CF has a block bound, numbered RVSDG has a θ bound, and linked coloured
Petri has a finite completed trace.
[Compiler and checked facts](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/Identification/Defs.lean)

`certify map admitted` retains the successful artifact and its source for
the existing equation and termination sentence forms. `corridor` maps
those sentences forward, pulls target valuations back, and checks
satisfaction. Both undefined partial words satisfy an equation between
them. Termination requires a finite return. This local corridor is for
successful compilations in the fixed pure five-block profile with fixed
primitive interpretation and result width.

## Run an identification

The fixture reads two distinct `i8` captures in an addition. The
identification maps both operands to a single target capture and keeps the
writable result in its own slot. The output triples are native at the
pullback, emitted CF, and emitted numbered RVSDG.

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Example
  (identify original conflicting changesAdmission aliasesWrite run refusal)

#eval original.toOption.map (fun admitted => (compile identify admitted).toOption.isSome)
-- some true

#eval (run true, run false)
-- (some (some 99, some 99, some 99), some (some 14, some 14, some 14))

#eval refusal identify conflicting
#eval refusal aliasesWrite original
#eval refusal identify changesAdmission
```

The three refusals exercise conflicting constants, a writable alias,
and a structurally safe contraction rejected by FIFO singleton admission.
[Checked regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/Identification/Regression.lean)
