# Native loop sentences on typed MLIR CF

Import `Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.Thms`.
A `Profile` fixes the ordered captured input widths, one latch width,
and one result width. `SourceSentence` admits the existing native loop
equations and termination assertions at that boundary. Its two sides
can have different producer tables. `translate` realizes the producer
symbols and lowers each loop to an actual typed CFG.
[Native loop sentences](sea-of-nodes-loop-institution.md) ·
[CFG lowering](sea-of-nodes-loop-mlir-cf.md)

A `Signature` supplies a typed opcode map into the concrete
profile of constants, flag-free addition and multiplication, and
unsigned comparison. A morphism commutes with realization and preserves
each ordered operand and result sort. The source room has one matched
model per signature, obtained by primitive reduct from the concrete
bit-vector model. The target room uses the one corresponding executable
CFG evaluator and the existing partial CFG observation.
[Room definitions](../../Silmaril/SSA/SeaOfNodes/Loop/MLIR/CF/Institution/Defs.lean) ·
[Lowering PR](https://github.com/hiloopai/silmaril-lean/pull/3356)

`encodeInput` and `sourceInputs` round-trip in both directions.
`translateProgram_observe` maps the source partial word into a
singleton returned CFG tuple. `equation_at_iff` reflects equality because
this result encoding is injective. Two undefined observations are
equal, and a return on only one side falsifies the equation.
`observe_none_iff` identifies undefinedness on the two sides.
`satisfaction_induced` extends that comparison to every input and
preserves and reflects universal termination as well.

```lean
module
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.Thms

open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution

example {B : Profile} (S : Signature) (s : SourceSentence B S.left) :
    (translate S s).Holds ↔ s.val.Holds (sourceModel S) :=
  satisfaction_induced S s
```

`model_reduct` identifies the matched source models along signature
maps. `translate_map` proves that renaming before realization gives the
same CFG sentence. These are the laws used in `compare_natural` and the
scoped `comorphism` into the fixed target room. Its model component
selects the matched source reduct of the sole target model.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Loop/MLIR/CF/Institution/Thms.lean)

The checked fixture returns 1 on one graph and proves undefinedness on
two graphs with different exit wires. The two divergent graphs satisfy
their equation, while the exiting graph and a divergent graph falsify
theirs. A nonidentity typed renaming swaps two local names for zero and
the translated equation is unchanged.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/MLIR/CF/Institution/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```

## Checked physical-layout replay

`Layout.run_fromTwo_run_eq` compares the emitted CFG directly with the
original CF lowering at every block fuel. It requires a successful
two-save `Replay.replay` of the same native loop with the nominated
header edits, a successful `Layout.initial?` on that seed, and a
successful `Layout.run` from position 2 on the finite suffix. Each
suffix cut is in the current physical preheader. The loop has captured
word inputs, one word latch and one word result. The concrete primitive
evaluator is total, while CFG execution may diverge.
[Layout replay](sea-of-nodes/optimization/sea-of-nodes-gcm-hoist-discovery.md#replaying-a-finite-list-of-physical-placements)

`run_fromTwo_translate_observe` applies that result to a native graph
with a typed realization into the concrete profile. The replay seed
must come from that realized graph. `observeCfg` uses the institution's
same partial denotation with the scheduled CFG's own typed block labels
and saved arguments. For every input, the emitted CFG and ordinary
translation have the same returned singleton or the same undefined
observation. Replacing either side of a partial equation, or the CFG in
a universal termination assertion, therefore preserves and reflects
its truth. No termination premise is required. A single exhausted fuel
budget establishes no divergence claim.
[Bridge theorems](../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/Institution/Thms.lean)

The scheduler moves total scalar lets in this profile. Its operation
and packet types cannot express memory loads or stores, ordering
tokens, observable calls, or trapping primitives. Effectful replay
would need those operations and their dependencies in the schedule and
an observation that accounts for their effects.

The regression seeds two hoists and replays three physical placements.
The generated preheader has seven lets, compared with two in the
original lowering. With inputs `(2, 10, 1)`, the generated CFG exhausts
fuel four and returns `9` at fuel five. With `(2, 10, 0)`, the latch
stays at `3` and the same generated CFG is undefined.
[Replay regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/Institution/Regression.lean)
