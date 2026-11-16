module

public import Silmaril.Sim.Reduce.PCalls.Defs
public import Silmaril.Proofs.Sim.Reduce.PCalls

/-!
# P-calls soundness for the certified G fragment: results

Proofs in `Silmaril/Proofs/Sim/Reduce/PCalls.lean`; every profile, every host relation, standard
axioms only.

* `stepCtx_of_stepFns`: **the method pieces** of a concrete simulator: functions running
  `emit i len` meet their step specifications (`Silmaril.Sim.X86.GCert.step_valid`).
* `calls_wp`: **a P-calls run exists**: from a store encoding `σ`, the body `call x₁ … call xₙ`
  of a program that retires on `Silmaril.X86.Ext.exec` runs (`Silmaril.Wasm.Logic.Core.WP`) to a
  store encoding the x86 result (composition of the existential step specifications by
  the call rule `wp_call`).
* `hwp_call_step`: the every-run call rule for a step method (a solver's tool for pieces).
* **`xproblem_of_piece`** (old name `reduce`): **P-calls soundness**: a solved `Piece` (every run of the P-calls body, the
  methods given only by their contracts) and a concrete simulator instance (`StepFns`, globals
  `0..22`) solve the x86 problem `Silmaril.Sim.X86.G.XProblem p Pre Post`. The proof joins the
  every-run piece with the existing run (no determinism argument is needed).
-/

/-- info: 'Silmaril.Sim.Reduce.PCalls.xproblem_of_piece' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.PCalls.xproblem_of_piece
