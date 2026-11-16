module

public import Silmaril.Wasm.Interp.ExampleEH.Defs
public import Silmaril.Wasm.Interp.EHSim.Thms
public import Silmaril.Wasm.Interp.EHClose.Thms
import Silmaril.Proofs.Wasm.Interp.ExampleEH

/-!
# A caught exception: theorems

`eh_run`: natively, `ehBody` throws the exception `0` (field `7`), the clause `catch $t 0` catches
it with the existing first-match resolution, and the block produces `7`. `eh_steps`: by the
exception simulation (`EHSim.evalOXE_good`), that is a Core 3.0 run, at every profile and host,
from the code to the value `7` in the store holding the exception. The code passes the exception
checker `ehExt ehTags` (`eh_chk`). `eh2_run`/`eh2_steps`: a rethrow, `catch_ref` then
`throw_ref`, ends natively and in Core in the thrown exception `0`. `eh3_run`/`eh3_steps`: two
parameters into an `if` and into a `try_table` whose body throws one of them; the block
produces `3`. `eh4_run`/`eh4_steps`: the exception of a callee answered by the closure with
exceptions (`EHClose.evalOXE_closed_good`) is caught around the call; the block produces `9`.
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

/-- **The rethrow, natively**: `catch_ref`, then `throw_ref`, throws the exception `0` again. -/
theorem eh2_run : Abstract.CallXE.EvalOXE ehC ehStore ehFrame [] ehBody2
    (ehStore', ehFrame, .throw 0) :=
  Silmaril.Proofs.Wasm.Interp.ExampleEH.eh2_run

/-- **The rethrow, in Core 3.0**: the run ends in the thrown exception `0`. -/
theorem eh2_steps : Steps P host ⟨ehStore, ehFrame, expression (Binaryen.BExpr.lowerList ehBody2)⟩
    ⟨ehStore', ehFrame, throwing 0⟩ :=
  Silmaril.Proofs.Wasm.Interp.ExampleEH.eh2_steps

/-- **Multi-value parameters, natively**: the `if` and the `try_table` each take two parameters;
the `try_table`'s body throws one of them, and the clause branches out of the block with it. -/
theorem eh3_run : Abstract.CallXE.EvalOXE ehC ehStore ehFrame3 [] ehBody3
    (ehStore3, ehFrame3, .normal [v3]) :=
  Silmaril.Proofs.Wasm.Interp.ExampleEH.eh3_run

/-- **Multi-value parameters, in Core 3.0**: the run produces `3`. -/
theorem eh3_steps : Steps P host ⟨ehStore, ehFrame3, expression (Binaryen.BExpr.lowerList ehBody3)⟩
    ⟨ehStore3, ehFrame3, vals [v3]⟩ :=
  Silmaril.Proofs.Wasm.Interp.ExampleEH.eh3_steps

/-- **A throwing callee, natively**: the closure answers the call with the callee's exception;
the clause catches it, and the block produces `9`. -/
theorem eh4_run : Abstract.CallXE.EvalOXE Abstract.XRecursionE.closedCallXE ehStore4 ehFrame4 []
    ehBody4 (ehStore4', ehFrame4, .normal [v9]) :=
  Silmaril.Proofs.Wasm.Interp.ExampleEH.eh4_run

/-- **A throwing callee, in Core 3.0**: the exception leaves the callee's frame and is caught; the
run produces `9`, no oracle assumed. -/
theorem eh4_steps : Steps P host ⟨ehStore4, ehFrame4, expression (Binaryen.BExpr.lowerList ehBody4)⟩
    ⟨ehStore4', ehFrame4, vals [v9]⟩ :=
  Silmaril.Proofs.Wasm.Interp.ExampleEH.eh4_steps

end Silmaril.Wasm.Interp.ExampleEH
