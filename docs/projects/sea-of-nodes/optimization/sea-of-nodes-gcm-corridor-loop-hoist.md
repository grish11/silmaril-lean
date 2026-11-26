# Hoisting a loop binding at the chosen GCM cut

Click's PLDI ’95 §§2.2–2.4 use definition and use bounds to choose a
placement in the shallowest loop nest, preferring the deepest dominator
position at equal depth. This slice connects that choice to emission for
one nominated pure total binding in the existing Sea-of-Nodes single-latch
loop lowered to typed MLIR CF. The existing chooser breaks remaining ties
by taking the first legal cut in enumeration order. [Proceedings][paper] ·
[Archived PDF][pdf] · [Corridor chooser][corridor]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
`LoopHoist.Corridor.pickAndHoist?` takes the native loop and a zero-based
header binding index. The existing binding resolver obtains the typed
operand origins through the preceding schedule and the exact use sites,
including the source, successor slot and argument index of each edge read.
The corridor chooser uses the three typed label numbers as identifiers. It
synthesizes a checked dominator tree from the actual lowered CFG, computes
loop depth and ranks the legal cuts. The selected cut goes directly to the
shared typed emitter. [Definitions][defs] ·
[Existing emitter][emitter]

The emitter accepts preheader cut zero with operands available as captured
inputs. A legal header cut is refused, with no fallback placement. The
supported CFG has an entry/preheader, a header with a self-backedge, and an
exit. This API covers one binding per call and assumes the pure total
operation profile of the native lowering. General CFG motion, dependency
slices and speculation of effectful or partial operations are outside its
scope. [Theorem header][thms]

`pickAndHoist?_placement` connects a successful rewrite to the synthesized
chooser, the actual nominated binding and the existing legality predicate.
`refuses_otherCut` covers every selected cut outside the emitter's insertion
point. `pickAndHoist?_routes` proves the captured value is carried on entry
and feedback and preserves the original exit transfer. `pickAndHoist?_run_eq`
gives exact equality at every CFG fuel. `pickAndHoist?_budget` preserves the
native loop's backedge-budget observation at fuel `budget + 3`.
`pickAndHoist?_denotePart` gives exact partial observation equality, including
undefined runs. [Theorem header][thms]

The example nominates binding 1, after a latch-dependent addition. In the
invariant variant, both preheader cut 0 and header cut 1 pass the checker.
The chooser selects the preheader, and the entry/header binding counts
change from `(2, 4)` to `(3, 3)`. One ordinary read and the header's
false-edge argument 0 use the moved result. At fuels 3, 4 and 5, the
multiple-feedback input yields `[none, none, some 2]`. The regression also
checks a zero-feedback input. With the latch-dependent operand, the
preheader cut fails the checker and the legal header cut 1 is selected and
refused. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example.Defs
cat >/tmp/gcm-corridor-loop-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example
#eval observe false -- (some (0, 0), some (3, 3, [none, none, some 2]))
#eval observe true  -- (some (1, 1), none)
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-corridor-loop-example.lean

make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GCM.Corridor.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[corridor]: sea-of-nodes-gcm-corridor-placement.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Defs.lean
[emitter]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Regression.lean
