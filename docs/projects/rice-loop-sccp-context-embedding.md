# Insert unused captures into a guarded SCCP entry

`TwoBackedges.ContextEmbedding.Embedding` is a finite typed sequence of
the existing register permutations and front weakenings. `insert S fresh i`
uses one front weakening followed by a permutation that puts the new
coordinate at the zero-based position `i`, including the end of the bank.
`insertValue` places a concrete value at that position. Every old port
maps injectively to a port of the same sort. `reduct_get` identifies the
value pulled back at each old port, and `reduct_trans` composes the
pullbacks in reverse order.
[Typed maps](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/Defs.lean) ·
[One-slot weakening](rice-loop-sccp-guarded-weakening.md)

`path.compile program` transports the admission evidence, runs the original
FIFO checker at the final signature, and invokes the existing guarded
emitters. The admitted side and coverage predicate agree with the original
on the pulled-back valuation. The old and new artifacts have independent
witnesses for each exact finite return. `compile_noReturn_iff` compares
absence of finite observation. For Petri the witness is a finite completed
trace of the linked net.
[Replay and observation laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/Thms.lean)

`compile_staged` compares the partial observations of two successive
successful compilations and one compilation along the composite.
`compile_congr` compares any two factorizations into the same final signature
that agree on all old typed ports. These comparisons establish equality of
returned words and definedness. The native and generated corridors reuse the
local satisfaction maps for partial equations and finite termination.
`nativeCorridor_trans`, `generatedCorridor_trans`, and `emit_commutes` attest
composition and the emission square. The API takes an explicit factorization
for the admitted pure five-block profile at fixed primitives and result
width. The existing [permutation institution](rice-loop-sccp-guarded-institution.md)
continues to use typed bijections as its signature arrows.

## Run the checker at a new entry

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Example
  (staged composed reordered route run)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Example
  (initialSignature original)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Example
  (capture captureWidth)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example
  (entry)
open Silmaril.SSA.SeaOfNodes.MLIR (Word)

def oneInsertion := insert initialSignature capture 1

#eval (oneInsertion.compile original).toOption.isSome
-- true

example (value : Word captureWidth) (side : Bool) :
    oneInsertion.reduct (insertValue (S := initialSignature) capture 1 value (entry true side)) =
      entry true side :=
  reduct_insertValue initialSignature capture 1 value (entry true side)

#eval [staged, composed, reordered].map route
-- [some true, some true, some true]

#eval [staged, composed, reordered].map (fun compiled => run compiled 0 false true)
-- [some (some 99, some 99, some 99), some (some 99, some 99, some 99), some (some 99, some 99, some 99)]

#eval [staged, composed, reordered].map (fun compiled => run compiled 65535 true false)
-- [some (some 7, some 7, some 7), some (some 7, some 7, some 7), some (some 7, some 7, some 7)]
```

The mixed-sort fixture inserts an `i16` after `again` and a Bool after
`select`. Each triple reports native, CF, and numbered results at their own
bounds. The regression checks that varying either fresh value preserves the
covered and fallback observations. It also checks the exact fallback return
for all three backend observers, including linked Petri.
[Checked regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/Regression.lean)
