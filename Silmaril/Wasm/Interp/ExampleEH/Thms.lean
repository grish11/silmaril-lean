module

public import Silmaril.Wasm.Interp.ExampleEH.Defs
public import Silmaril.Wasm.Interp.EHSim.Thms
import Silmaril.Proofs.Wasm.Interp.ExampleEH

/-!
# A caught exception: theorems

`eh_run`: natively, `ehBody` throws the exception `0` (field `7`), the clause `catch $t 0` catches
it with the existing first-match resolution, and the block produces `7`. `eh_steps`: by the
exception simulation (`EHSim.evalOXE_good`), that is a Core 3.0 run, at every profile and host,
from the code to the value `7` in the store holding the exception. The code passes the exception
checker `ehExt ehTags` (`eh_chk`).
-/

public section

namespace Silmaril.Wasm.Interp.ExampleEH

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {P : Numerics.Profile} {host : HostSemantics Empty}

/-- **The native run.** -/
theorem eh_run : Abstract.CallXE.EvalOXE ehC ehStore ehFrame [] ehBody
    (ehStore', ehFrame, .normal [v7]) :=
  Silmaril.Proofs.Wasm.Interp.ExampleEH.eh_run

/-- The code passes the exception checker; the block produces one value. -/
theorem eh_chk : chkE (ehExt ehTags) ehStore.funcs ehMod 0 0 [] (some 0) ehBody = some (some 1) :=
  Silmaril.Proofs.Wasm.Interp.ExampleEH.eh_chk

/-- **The Core 3.0 run** through `throw` and the handler's catch, to the value `7`. -/
theorem eh_steps : Steps P host ⟨ehStore, ehFrame, expression (Binaryen.BExpr.lowerList ehBody)⟩
    ⟨ehStore', ehFrame, vals [v7]⟩ :=
  Silmaril.Proofs.Wasm.Interp.ExampleEH.eh_steps

end Silmaril.Wasm.Interp.ExampleEH
