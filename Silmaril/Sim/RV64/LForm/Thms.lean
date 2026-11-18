module

public import Silmaril.Proofs.Sim.RV64.LForm

/-!
# Specialised per-instruction code (the L-form): results

Proofs in `Silmaril.Proofs.Sim.RV64.LForm`, total correctness, every profile and host relation:

* **`lInstr_twp`**: the chunk `lInstr i` (`add/sub/xor/or/and`, `addi/xori/ori/andi`, `lui`)
  terminates with memory `B'`, `absState B' = Silmaril.RiscV.step i (absState B)`, changed only
  in the register block: the specialised semantics of `step` on the word `encode i`;
* **`lProg_twp`**, **`lProg_refines`**: the composed L-form `lProg is` of a straight-line
  program runs the reference steps in order; from `pc = 0x1000` the reference machine running
  the actual words `is.map encode` at `0x1000` reaches the final abstract state after exactly
  `|is|` steps (`refRun_codeAt`);
* `lAlu_vc` (one generic `wpc` proof for every register choice), `wpc_opnd`, `wpc_c64`,
  `wpc_binop`.
-/
