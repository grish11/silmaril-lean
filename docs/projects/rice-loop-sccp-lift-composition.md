# Compose checked capture-map lifts

For the pure guarded five-block profile, take two typed capture maps
`first : PortMap S T` and `second : PortMap T U`. The original valuation
lies in the image of the composed reduct exactly when it has an intermediate
lift that is fibre-consistent for `second`. Equivalently, its values agree
whenever two old ports reach the same final port.
[Typed port composition](rice-loop-sccp-port-composition.md) ·
[Single-map image and lift](rice-loop-sccp-port-factorization.md)

`LiftComposition.liftStaged first second oldInput finalFill` returns
`some (mid, target)` exactly when the two reducts recover `mid` and
`oldInput`, and `target` keeps `finalFill` at every final port unused by
the composition. Its final valuation is exactly the result of the existing
one-shot `liftChecked` for the composed map. Refusal means a disagreement
in a composed fibre.

The intermediate fill is the second reduct of the final candidate
reconstructed from the old input. An intermediate slot unused by the first
map can share a final slot with a used intermediate slot. In that case the
old input determines both values. Simply pulling back the raw fill can
make those intermediate values disagree.
[Checked lift laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/LiftComposition/Thms.lean)

`LiftComposition.compare first second admitted` runs the existing guarded
compiler at the intermediate signature, at the final signature using the
intermediate result, and independently for the composed map. Refusals
carry the failing step and its reason. The valuation theorem applies
independently of the checker outcomes. The compiler comparison requires
three successful calls.

For a sentence over successful `Compared` operands, `satisfaction_at_lift`
pulls equation or termination truth from the staged final artifact to the
actual intermediate artifact and then to the old source. It also compares
the direct final artifact to that source. `satisfaction_coherent` compares
staged and direct truth even when the unused target fills and the chosen
backends differ. Both lifts must reduce to the same original input.
`coverage_at_lift` and `observations_at_lift` give the corresponding
guard and partial-word laws. Both undefined words satisfy an equation
between them. Termination requires a finite return. For linked coloured
Petri the witness is a finite completed trace.

## Run the example

The first map identifies two `i8` addends. The second identifies the used
and unused intermediate addend slots, and leaves an interior final `i16`
unused. The final fill supplies zero at the shared slot. The checked
staged lift reconstructs 7 there. The outputs of `run` show intermediate,
staged-final and direct-final results, each ordered as CF and numbered
RVSDG with separate budgets.

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Example
  (liftValues naiveSucceeds compared compilerRefusal run)

#eval (liftValues 7 0, liftValues 7 65535, liftValues 8 65535)
-- (some (7, 0), some (7, 65535), none)
#eval (naiveSucceeds, compared.isSome)
-- (false, true)
#eval run 65535 true
-- Each emitted artifact returns 99.
#eval run 0 false
-- Each emitted artifact returns 14.
#eval compilerRefusal
-- The first compiler call reports neitherMarked for the alternate program.
```

[Checked regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/LiftComposition/Regression.lean)
