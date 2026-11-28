# Recover the selected Φ row from a bounded compact CFG run

`Phi.Run.admitted` checks that the actual entry reaches the header for the
given input and that the header has a branch terminator. `firstExit?` then
walks the actual header evaluations with the existing CF block budget. It
records the taken slot, the last header environment, the exit packet, the
number of feedback transfers, and the remaining fuel. Branch selection
uses the CF guard and retains the slot even when both arms target the same
exit. This gives the dynamic counterpart of Click's incoming-occurrence
rule for Φ reads in Schedule Late (§2.3). [Definitions][defs] · [Click PLDI ’95][paper]

`run_split` factors the existing CF evaluator into this prefix and the
ordinary exit continuation. `firstExit_selected` verifies the taken slot
and the budget accounting. The prefix consumes one entry block and one
header visit per feedback, plus the header visit that takes the exit edge.
Arriving with zero remaining fuel still exhausts the ordinary run.
[Theorems][thms]

On a successful compact run, `recover_of_run` gives the selected
`PhiView` row and its latched compact packet. The full CFG reaches the same
occurrence with the same header environment at common CF fuel.
`firstExit_project` proves that the emitter's ordered typed projection
relates the two arriving packets. `Recovery.transfer_iff` uses the
existing local λSSA branch-transfer law to carry the projected packet
and preserve branch state. Whole-program partial observations continue
to use the existing compaction theorem. The profile is the saved-loop
label family with checked entry to the header and with a returning compact
exit. Budget accounting here is for typed CF. [Theorems][thms] · [Compaction][compact] · [Positional Φ bridge][phi]

The interleaved fixture returns after zero or two feedback transfers,
projecting slots `[4, 6, 8]` on both runs. The shorter budget reaches the
exit after two feedback transfers with zero fuel left and yields no
return. The parallel fixture reaches the same exit from the same header
with either guard. The true slot latches `[7]` and the false slot latches
`[9]`. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Regression
cat >/tmp/gcm-selected-exit-phi.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Example
#eval immediate
#eval afterFeedback
#eval arrivedWithoutReturn
#eval parallel 1
#eval parallel 0
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-selected-exit-phi.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[compact]: sea-of-nodes-gcm-compact-exit.md
[phi]: sea-of-nodes-gcm-compact-exit-phi.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Phi/Run/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Phi/Run/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Phi/Run/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Phi/Run/Regression.lean
