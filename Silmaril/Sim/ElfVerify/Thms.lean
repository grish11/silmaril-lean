module

public import Silmaril.Proofs.Sim.ElfVerify.Bswap
public import Silmaril.Proofs.Sim.ElfVerify.BswapOpen9
public import Silmaril.Proofs.Sim.ElfVerify.SatAdd

/-!
# Real ELF functions through the ISA → Wasm reduction: results

Proofs in `Silmaril.Proofs.Sim.ElfVerify.*`. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

* **`bswap_sysv`**: `bswap32_manual` (`89 f8 0f c8 c3`) meets its System V contract on the
  `Silmaril.X86.Ext` machine (`AbiEntry`, first return to the sentinel, `AbiReturn`,
  `rax = zext (bswap32Spec edi)`), for every descriptor and caller with defined modelled flags;
  the functional part is the Wasm proof `bswap_wasm` (`wpc` over the G code of `Silmaril.Sim.X86.G`), carried
  over by `Silmaril.Sim.SysV.xgoal_of_body`.
* **`bswap_in_elf`**: those bytes are what the pinned `leaf-arith` executable loads at
  `0x401420`.
* `bswap32Spec_eq`: the ladder's C spec is silmaril's `byteSwap32`.
* **`bswapSpec_total_open9`**: the ladder's own spec `Ladder.LeafArith.bswapSpec` on
  `Open9.isa`, through the reduction; `bswapContract_same`: same spec as the ladder's
  `bswap32_manual_contract.toOpen9` (`rfl`).
* **`SatAdd.satSpec_total_open9`**: `sat_add_u32` (branches, a backward `jmp`, two `ret`s): the
  ladder's own `satSpec` on `Open9.isa`; functional part and termination from Wasm (the
  dispatcher of `Silmaril.Sim.X86.Loop`, `wasm_solution`, and the ranking `ranked` through `Silmaril.Sim.Reduce.Loop.xrun_of_ranked`);
  `satContract_same` (`rfl`).
-/

/-- info: 'Silmaril.Sim.ElfVerify.bswap_sysv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.ElfVerify.bswap_sysv

/-- info: 'Silmaril.Sim.ElfVerify.bswap_in_elf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.ElfVerify.bswap_in_elf

/-- info: 'Silmaril.Sim.ElfVerify.bswapSpec_total_open9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.ElfVerify.bswapSpec_total_open9

/-- info: 'Silmaril.Sim.ElfVerify.SatAdd.satSpec_total_open9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.ElfVerify.SatAdd.satSpec_total_open9
