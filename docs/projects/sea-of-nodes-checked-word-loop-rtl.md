# Checked Sea of Nodes word loops in machine RTL

`Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.lower` checks a native
`Loop.Graph` with two 64-bit inputs (seed and stride), one carried word,
an empty preheader, and three header producers. The first producer
wraps `old + stride` or `old - stride`. The second is a word constant.
The third compares the update and the constant using equality or
inequality. True feeds back the update. False returns the old word.
[Native loop][source] · [Checked definitions][defs] · [Original bridge][countdown]

`Checked.recognize_eq_some_iff` characterizes success by equality with
`Profile.graph`. The matcher checks producer operand addresses, separate
entry and feedback operands, the predicate, and the return wire. A valid
typed wire can still be outside the admitted profile.

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Thms`. Given
`ok : Checked.lower graph = some target`, use `Checked.lower_wellFormed ok`
for the machine program check and `Checked.lower_returns_iff ok`
to translate finite returns in either direction, with a singleton word
and the entire memory unchanged. `Checked.lower_stepsN_iff ok` relates
exactly `n` native backedges to `4 * n + 5` running steps followed by
the terminal return step. The count includes the entry jump and the
three instructions and branch of every header activation.
[Theorem header][thms] · [Machine evaluator][machine]

The regression checks the original countdown and a graph with addition,
an equality branch and a nonzero bound. It rejects a constant in the
update position and a same-type limit wired in place of the feedback.
The theorems concern finite runs of pure single loops with this producer
schedule, provenance, and single carried word.
[Regression][regression]

## Lower the same checked graph to explicit-φ λSSA

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi.Thms
import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Thms

open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (entry model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL (Profile)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def addUntilDifferent : Profile := ⟨.add, 7, .eq⟩

#eval (Phi.lowerChecked addUntilDifferent.graph).map fun (rtl, ssa) =>
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain 10 0 [5, 2] mem).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model (entry 5 2)) 2 ssa).bind fun (_, packet) =>
    (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
  (machine.map (List.map BitVec.toNat), typed.map BitVec.toNat)
-- some (some [7], some 7)
```

`Phi.lowerChecked` uses the existing native matcher to admit both targets.
`Phi.lowerChecked_typed` certifies machine well-formedness and λSSA typing.
Use `Generic.phiView` on the original graph to inspect the occurrence-indexed
Φ view of the generated λSSA. `Phi.incoming_alignment` relates either
positional presentation to RTL's actual source block and successor ordinal.
`Phi.entry_slot_transfer_iff` and `Phi.feedback_slot_transfer_iff` specify
the whole packet read by each of those branches. [Theorem header][phi-thms] ·
[Generic Φ lowering][generic-phi]

`Phi.activation_agrees` runs all three emitted producers and the branch in
both targets. The runtime guard selects feedback with the updated tuple
or exit with the old word. `Phi.returns_iff` composes that profile's existing
finite semantics with the typed CFG and preserves the entire memory.
For seed `5` and stride `2`, the equality guard first transfers `7`, and
the next visit exits with `7`. For seed `6` and stride `2` it exits on
the first visit with `6`. The regression checks both predecessor orders
and rejects a guard wired to the old bank in place of the update.
The profile carries one i64, compares against a fixed i64 limit, and uses
the existing total add/sub and eq/ne operations. [Paired regression][phi-regression]

```sh
lake build --wfail +Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Thms \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Checked.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Regression \
  +Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi.Thms \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Checked.Phi.Regression
lake env leanchecker Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Correctness
lake env leanchecker Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Thms
```

[source]: ../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean
[defs]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Checked/Defs.lean
[thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Checked/Thms.lean
[countdown]: sea-of-nodes-loop-rtl.md
[machine]: ../../Silmaril/Raw/Machine/RTL/SSA.lean
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Checked/Regression.lean
[phi-thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Checked/Phi/Thms.lean
[generic-phi]: sea-of-nodes/control-flow/sea-of-nodes-loop-lambdassa-generic.md
[phi-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Checked/Phi/Regression.lean
