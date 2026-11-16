module

public import Silmaril.Sim.Reduce.Loop.Defs
public import Silmaril.Proofs.Sim.Reduce.Loop

/-!
# Termination and frame of dispatcher runs from Wasm rankings: results

Proofs in `Silmaril/Proofs/Sim/Reduce/Loop.lean`; standard axioms only. Generic over the table:

* per instruction form (the whole `emitX` fragment): `frame_of_exec` (no register
  outside `writesOf` changes), `emitX_progress` (retires on defined flags), `progress_nf`
  (flag-free forms always retire), `flags_out` (`flagOut` is sound), `rip_succ` (`succs`);
* **`xrun_of_ranked`**: a Wasm ranking (`Ranked`) of the dispatcher and the decidable flag
  dataflow check (`flagsOK`) give an x86 table run from every encoded state satisfying the flag
  invariant, with every register outside `tabWrites` unchanged; `flagInv_entry` (the
  invariant holds at the entry);
* `run_of_xrun` (table runs are `Ext.stepOpt` runs), `bytesAt_of_loaded`.
-/

/-- info: 'Silmaril.Sim.Reduce.Loop.xrun_of_ranked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.Loop.xrun_of_ranked
