module

public import Silmaril.Sim.Core.Defs
public import Silmaril.Proofs.Sim.Core.PState
public import Silmaril.Proofs.Sim.Core.Run
public import Silmaril.Proofs.Sim.Core.Lattice
public import Silmaril.Proofs.Sim.Core.Repr
public import Silmaril.Proofs.Sim.Core.Cfg

/-!
# Simulators: what is proved (header)

PROVED (standard axioms; proofs in `Silmaril/Proofs/Sim/Core/{PState,Run,Lattice}.lean`, names
in `Silmaril.Sim`):

* **Partial states** (`PState`): `⊑` is a partial order (`Le.refl`, `Le.trans`,
  `Le.antisymm`), `bot_le`, `le_ofTotal_iff`; `comap_mono`; `join` is the least upper bound of
  compatible states (`le_join_left`, `le_join_right`, `join_le`, `compat_of_le`); `meet` is the
  greatest lower bound (`meet_le_left`, `meet_le_right`, `le_meet`); `override_le`;
  `comap_pushAlong` (for injective maps); `Mono.comap`.
* **Runs**: `Star.{single, trans, mono, sim}`; `Machine.sem_reduct` (a reduct runs the
  substituted program); `Prog.MonoTests.subst`.
* **Soundness lifts from steps to runs**: `Simulation.sem` (guards upward closed),
  `CoSimulation.sem`; simulations compose and survive reducts: `Simulation.{refl, trans,
  reduct}`, `Sound.{refl, trans}`, `CoSimulation.{refl, trans, reduct}`,
  `Complete.{refl, trans}`, `Equiv.{toSimulation, toCoSimulation, symm}`.
* **Transfer** (the core of the reduction "simulator property ⇒ ISA property"):
  `Simulation.angelic` (angelic total correctness with an upward-closed postcondition),
  `Simulation.hAngelic` (hidden states: arbitrary pre/post linked through the relation),
  `Simulation.progress`, `CoSimulation.demonic`, `CoSimulation.hDemonic`,
  `Machine.angelic_of_demonic` (demonic partial correctness + progress ⇒ angelic).
* **Decomposition rules**: `Machine.HAngelic.{conseq, skip, seq, choice_left, choice_right,
  star_of_measure}`, `Machine.HDemonic.{conseq, skip, seq, choice, star}`.
* **The lattice of partial-state simulators** (`PRel`): `Le.{refl, trans}`; `Sound.mono`
  (soundness is downward closed); `bot_le`, `bot_sound`, `havoc_sound_iff`;
  `le_sup_left`, `le_sup_right`, `sup_le`, `Sound.sup`, `le_sSup`, `sSup_le`, `Sound.sSup`;
  `best_sound`, `sound_iff_le_best` (the sound simulators are exactly those below `best`);
  `meet_le_left`, `meet_le_right`, `le_meet`, `Sound.meet_left`; `Sound.combine` (information
  join, deterministic reference), `le_combine_left`; `Sound.frame`, `Sound.lift`,
  `Sound.liftCmd`; `Sound.simulation`, `Sound.sound`.
* **Deterministic references** (`Machine.ofStep`, `Prog.loop`): `Machine.ofStep_sem_loop_iff`
  (running to completion is `Silmaril.Machine.Execution.Reaches`), `Machine.hAngelic_ofStep_iff`
  (angelic correctness of `loop` is the `FnContract.Spec.Total` shape), **`Simulation.reaches`**
  (a `Reaches` goal on the ISA from an angelic property of a sound simulator),
  `Machine.HAngelic.of_rel` (a one-call `run` export implementing `loop`).
* **Wasm obligations**: `Simulation.ofMethods`, `WasmSim.Obligations.simulation`,
  `WasmSim.Obligations.sound` (per-export partial-correctness triples give soundness).
* **Oracles** (`PSim`): `sound_iff` (demonic oracle soundness is soundness of the behaviour
  relation), `Sound.soundSome`, `Complete.coSimulation`; `SoundExact.simulation`,
  `SoundExact.exact`, `SoundExact.exactSound` (a simulator drawing undefined values from the
  oracle is an exact simulation).
* **General and exact simulations**: `Prog.allTests_true`, `FwdSim.semWith` (runs, for a class
  of guards transported by the relation), `FwdSim.hAngelic`; `Simulation.semExact`,
  `Simulation.angelicExact` (exact simulations transfer angelic properties with arbitrary
  guards and postconditions: branching on oracle-drawn flags), `ExactSound.sound`.
* **Demonic total correctness** (`Machine.Must`, the `RelIsa.Must` shape): `Must.mono`,
  `Must.of_measure` (termination from per-step triples with a decreasing measure),
  `Must.exists_run`, **`CoSimulation.must`** (transfer from a complete simulator whose stopped
  states reflect the reference's).

* **Representations** (`Repr`): `Equiv.{refl, trans, sem, semBwd, reduct}`,
  `Sound.of_equiv`, **`Sound.of_repr`** (G ≡ M through a shared core: only the accessor machines
  must be equivalent); `FwdSim.{refl, trans}`, `Prog.block_allTests`,
  **`FwdSim.block_transfer`** (L: specialised straight-line code, chunk by chunk).
* **Control flow** (`Cfg`): `Machine.sem_choiceList_iff`, `Prog.choiceList_allTests`,
  `Prog.cfg_allTests`; cut points `Machine.HAngelic.cfg_of_measure` (invariants at loop
  headers + measure), `Machine.HDemonic.cfg`; **`FwdSim.prog_transfer`** (the L-form with
  branches and loops, upward-closed guards, views of L equal to the simulator's).

`Silmaril/Sim/Machine/Thms.lean` relates `Machine.Must` to `RelIsa.Must`.
-/
