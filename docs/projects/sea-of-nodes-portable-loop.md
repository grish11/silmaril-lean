# One pure Sea of Nodes loop in three targets

The example is one `Loop.Graph` with a single `i8` latch and captured
`start`, `limit`, and `step` inputs, in that order. It starts at
`start`, adds `step` while the latch is unsigned-less-than `limit`,
and returns the final latch plus `start`. Arithmetic wraps modulo 256.
All three lowerings accept this same graph and concrete primitive model.
[Example graph](../../Silmaril/SSA/SeaOfNodes/Loop/Portable/Example/Defs.lean)

## Run the example

Use the repository's pinned Lean toolchain and run this from the repository
root. [Toolchain setup](../development.md)

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.Loop.Portable.Example.Defs
```

Paste the entire block into `SeaOfNodesExample.lean`, then run
`lake env lean SeaOfNodesExample.lean` from the same root.

```lean
module

import Silmaril.SSA.SeaOfNodes.Loop.Portable.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Loop.Portable.Example.Defs

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Loop.Portable

-- Native run: three backedges from 2 to 5, then return 5 + 2.
#eval (Example.graph.evalBackedges Loop.MLIR.CF.model 3
  (MLIR.sourceInputs (Example.input 2 5 1))).map (fun value => value.toNat)
-- some 7

-- Arguments are the backedge budget, start, limit, and step.
-- The pair contains the numbered θ result and the MLIR CF result.
#eval Example.run 3 2 5 1   -- (some 7, some 7), three backedges
#eval Example.run 0 5 5 1   -- (some 10, some 10), immediate exit
#eval Example.run 1 4 5 1   -- (some 9, some 9), one backedge
#eval Example.run 2 2 5 1   -- (none, none), too few backedges
#eval Example.run 3 2 5 0   -- (none, none), zero step below the limit

example : Agreement Example.graph (Example.input 2 5 1) :=
  agreement Example.graph (Example.input 2 5 1)
```

`Example.run` executes the graph after `Loop.Graph.lowerTheta` and after
`Loop.MLIR.CF.lower`. `agreement` relates the targets through the native
`Part` result.
Its `lambda_eval_iff` field characterizes every finite λSSA evaluation
with unit ambient state. An exit has external label zero and a packed
singleton payload. Its `theta` and `cf` fields identify the exact
partial observations with the source result encoded as a singleton tuple
and a singleton `.returned` outcome, respectively. The checked fixture
uses successful actual θ runs to derive the observations in all three
targets. For step zero with start 2 and limit 5, an invariant fixes the
latch at 2. There is no finite λSSA evaluation at any exit label, and
both target partial observations equal `Part.none`.
[Public theorem](../../Silmaril/SSA/SeaOfNodes/Loop/Portable/Thms.lean) ·
[Checked cases](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/Portable/Regression.lean)

| Evaluator | Budget |
| --- | --- |
| Native bounded loop | A budget of `b` permits `b` completed backedges and still tests the header at zero. |
| Numbered RVSDG θ | The example allows `b + 1` body activations. A successful run includes the final stop test. |
| Typed MLIR CF | The example supplies `b + 3` blocks, covering entry, up to `b` continuing headers, the final header, and exit. |
| λSSA `Region.Eval` | Finite evaluation is a relation with an explicit CFG-follow derivation. It has no numeric run budget. |

A bounded `none` can mean budget exhaustion. Undefinedness in
`agreement` concerns all finite returns. The theorem covers the pure
single-latch CF profile with word inputs, a word result, and the matched
constants, flag-free arithmetic, and unsigned comparison. It compares
return observations for these lowerings in their induced models.
[Generic λSSA adequacy](../../Silmaril/SSA/SeaOfNodes/Loop/LambdaSSA/Generic/Thms.lean) ·
[Numbered θ adequacy](../../Silmaril/SSA/SeaOfNodes/Loop/Theta/Thms.lean) ·
[MLIR CF adequacy](sea-of-nodes-loop-mlir-cf.md)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Loop.Portable.Example.Defs +Silmaril.Proofs.SSA.SeaOfNodes.Loop.Portable.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Loop.Portable.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```

## Continue exploring

- [Straight-line memory and explicit state](sea-of-nodes/memory/sea-of-nodes-memory.md)
- [Global code motion for one floating value](sea-of-nodes/optimization/sea-of-nodes-gcm-discovery.md)
- [Sparse conditional constant propagation on a typed diamond](rice-diamond-sccp.md)
