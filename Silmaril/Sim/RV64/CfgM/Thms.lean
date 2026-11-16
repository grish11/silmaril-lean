module

public import Silmaril.Proofs.Sim.RV64.CfgM

/-!
# Cut points with memory reads: results

Proofs in `Silmaril.Proofs.Sim.RV64.CfgM`: `cfgSymM_sound` (blocks with `ld` are followed by every
concrete `Ext` run whose block outcome is defined: every load aligned and readable, checked by
`TreeM.chk` even when the loaded value is dead), **`reach_blockM`**.
-/
