module

public import Silmaril.Wasm.Abstract.SRelabelPull.Defs
public import Silmaril.Wasm.Abstract.InstSessionD.Defs
public import Silmaril.Games.DPull.Thms

/-!
# The session relabelling as a generic pull: theorems

The concrete read-backs `spull` and `spullD` are the generic pulls along `srelabel`
(`spull_eq_pull`, `spullD_eq_pull`). So the generic laws of `Silmaril.Games.DPull` apply:
the finite plays, divergences and infinite plays are the preimages
(`DStrategy.mem_toStrategy_pull`, `mem_div_pull`, `mem_inf_pull`), and pulling is monotone
(`DStrategy.pull_mono`) and a congruence (`DStrategy.pull_congr`). Taking
`spullD σ := σ.pull srelabel posAns pullData_srelabel` in `InstSessionD.Defs` changes no
statement there: `spullD_eq_pull` is then `rfl` up to `spull_eq_pull`.
-/

public section

namespace Silmaril.Wasm.Abstract.InstSession

open Silmaril.Games
open Silmaril.Wasm.Game Silmaril.Wasm.Component.Reference

variable {E : Sig.{0}} {ts : List FnType}

/-- **`spull` is the generic pull along `srelabel`.** -/
theorem spull_eq_pull (σ : Strategy E (ssig ts)) :
    spull σ = σ.pull srelabel posAns pullData_srelabel :=
  (Strategy.pull_eq_generate pullData_srelabel σ).symm

/-- **`spullD` is the generic pull along `srelabel`.** -/
theorem spullD_eq_pull (σ : DStrategy E (ssig ts)) :
    spullD σ = σ.pull srelabel posAns pullData_srelabel :=
  DStrategy.ext (spull_eq_pull σ.toStrategy) rfl rfl

end Silmaril.Wasm.Abstract.InstSession
