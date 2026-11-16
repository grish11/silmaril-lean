module

public import Silmaril.Proofs.Sim.RV64.Mem.Sound
public import Silmaril.Proofs.Sim.RV64.Mem.Image

/-!
# An RV64 simulator in Wasm with the register file in linear memory: results

Proofs in `Silmaril.Proofs.Sim.RV64.Mem.{Lemmas,Step,Sound}`, at every profile and for every host
relation, **total correctness** (every call terminates):

* **`step_sound`**: the function `step` of `simM` (fetch from its own memory, decode, execute all
  21 instructions of `Silmaril.RiscV.Instr`) meets `stepSpec`: status `0` retires exactly one
  reference step `refStep (absCode B) (absState B)` (fetch, `Silmaril.RiscV.decode`,
  `Silmaril.RiscV.step`) and writes only the register block; status `2`/`3` leaves memory
  unchanged exactly where the reference machine stops;
* `absCode_of_sameOutside`, `wf_of_sameOutside`: a retired step keeps the code and the size.

What is not claimed: the reference has no memory access, branches or traps; the simulator's
code region is fixed to `[0x1000, code_end)` with `code_end ≤ 0x10000` (other `pc`s fault).
-/
