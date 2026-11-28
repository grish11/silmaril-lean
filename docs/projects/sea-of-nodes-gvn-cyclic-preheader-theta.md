# Emit normalized cyclic GVN as numbered RVSDG θ

`Theta.emit` runs native preheader-seeded GVN until the existing proposal
checker accepts no further deletion, then passes the restored graph to
`Loop.Graph.lowerTheta`. The original graph goes
through that same emitter directly. Both programs use the original typed
input and result interface. `emit_entry` equates the numbered preheader
and θ entry node labels and their complete ordered input addresses. This
includes the captures and every entry Φ operand.
[Emission API](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Iteration/Preheader/Theta/Thms.lean) ·
[Native normalization](sea-of-nodes-gvn-cyclic-preheader-iteration.md) ·
[Numbered θ lowering](../../Silmaril/SSA/SeaOfNodes/Loop/Theta/Thms.lean)

`emit_returns_iff` relates executions of the two emitted graphs at the
same input. Each graph has its own finite witness in the existing
numbered evaluator. `emit_observe` equates their partial denotations,
including absence of any finite return. A bounded run can exhaust its
budget before a return. The partial observation quantifies over all
finite executions.
[Numbered evaluator and finite-return bridge](../../Silmaril/SSA/RVSDG/NestedTheta/Thms.lean)

```lean
module
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta.Thms

open Silmaril.SSA.SeaOfNodes
open Diamond (Ty ValueSort sortValue)
open GVN.Cyclic.Activation (Inputs)
open GVN.Cyclic.Builder.Preheader (Native)
open GVN.Cyclic.Iteration.Preheader.Theta
open Pure.SubZero (model)

example {args carried : List (ValueSort Unit)} {entry header : List (List (Ty Unit))}
    {out : ValueSort Unit} (g : Native args carried entry header out)
    (input : Inputs model args) (result : sortValue model.value out) (originalFuel : Nat)
    (returned : g.lowerTheta.run (Loop.thetaRuntime model) originalFuel input =
      some (.cons result .nil)) :
    ∃ fuel, (emit g).run (Loop.thetaRuntime model) fuel input = some (.cons result .nil) :=
  (emit_returns_iff g input result).mpr ⟨originalFuel, returned⟩
```

The native fixture shrinks from five header producers to four and then
three. The numbered θ bodies contain six, five and four nodes,
including the routing node. The three emitted preheader additions keep
their operands, and the θ entry still reads all four Φ lanes in order.
With original inputs `(true, false, 3, 4)`, the original numbered graph
returns 99 at bound 2 and the normalized graph returns 99 at bound 3.
With inputs `(true, true, 3, 4)`, the predicate stays true on
every backedge and both partial observations are absent.
[Checked fixture and numbered runs](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/Iteration/Preheader/Regression.lean)

```sh
topic=SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader
make check CHECK_TARGETS="+Silmaril.$topic.Theta.Thms +Silmaril.Proofs.$topic.Regression"
lake env leanchecker "Silmaril.$topic.Theta.Thms"
lake env leanchecker "Silmaril.Proofs.$topic.Regression"
```

Click PLDI ’95 §3.1 step 3 motivates replacing redundant producers and
deleting the unused computations. The existing native pass supplies
those checked eliminations, with cyclic classes computed from ordered
use-def occurrences as in the Rice thesis §§4.1–4.2. The emission proof
covers the pass's return observations in the numbered θ target. The
target may recompute the final pure header to read the exit, so the
the observation is limited to finite return behavior. The typed MLIR CF
word-bank emitter currently expects a different opcode family and
word-only input and carried banks. The fixture uses predicate lanes,
which the generic θ emitter admits directly.
[Pinned Click PLDI ’95 PDF and citation](sea-of-nodes-gvn-cyclic-pass.md#sources) ·
[Rice thesis](https://hdl.handle.net/1911/16807) ·
[Typed MLIR CF bank](../../Silmaril/SSA/SeaOfNodes/Loop/MLIR/CF/Defs.lean)
