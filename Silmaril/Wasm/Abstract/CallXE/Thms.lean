module

public import Silmaril.Wasm.Abstract.CallXE.Defs
import Silmaril.Proofs.Wasm.Abstract.CallXE.Basic

/-!
# The extended relation with exceptions: theorems

`EvalOXE` is a **conservative** extension of `CallX.EvalOX`:

* `EvalOXE.of_evalOX`: every `EvalOX` run is an `EvalOXE` run, with the same outcome;
* `evalOXE_iff_evalOX`: on code without `throw`, `throw_ref` and `try_table` (`ehFreeL`), the
  two relations are the same.

So every theorem about `EvalOX` (Core adequacy, closure, divergence) holds unchanged on
exception-free code, and the exception rules only add runs of the exception forms.
-/

public section

namespace Silmaril.Wasm.Abstract.CallXE

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallX

variable {H : Type}

/-- **Every `EvalOX` run is an `EvalOXE` run.** -/
theorem EvalOXE.of_evalOX {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalOX C s f stk es r) :
    EvalOXE C s f stk es r :=
  Silmaril.Proofs.Wasm.Abstract.CallXE.of_evalOX h

/-- **Conservativity**: on exception-free code, `EvalOXE` is `EvalOX`. -/
theorem evalOXE_iff_evalOX {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (hx : ehFreeL es = true) :
    EvalOXE C s f stk es r ↔ EvalOX C s f stk es r :=
  ⟨fun h => Silmaril.Proofs.Wasm.Abstract.CallXE.to_evalOX h hx, EvalOXE.of_evalOX⟩

end Silmaril.Wasm.Abstract.CallXE
