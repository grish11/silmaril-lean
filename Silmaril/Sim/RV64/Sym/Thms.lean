module

public import Silmaril.Proofs.Sim.RV64.Sym

/-!
# A symbolic executor for RV64 leaf functions: results

Proofs in `Silmaril.Proofs.Sim.RV64.Sym`:

* **`extSym_sound`**: `extSym code n pc regs = some T` ⇒ every `Ext` run from a matching state
  returns to `ra` with `a0 = T.eval σ` and `sp`, `s0`–`s11` preserved (proved once);
* `regs0_eval`, `Tree.eval_congr` (a tree's value depends only on `Tree.varsIn` registers).
-/
