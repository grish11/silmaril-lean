module

public import Silmaril.Wasm.Abstract.XClosing.Defs
public import Silmaril.Wasm.Abstract.XRecursion.Thms
import Silmaril.Proofs.Wasm.Abstract.XClosing.Basic
import Silmaril.Proofs.Wasm.Abstract.XClosing.Direct

/-!
# The extended call forms as an open abstract module: theorems

* **Closure agreement.** The generic closing `Shape.close` of the open module
  `wasmOpenX` (every call form an internal call) gives exactly the closed
  outcomes of the extended recursive semantics `XRecursion.closedCallX`
  (`close_wasmOpenX`). This holds for every store, typed or not.
* **The direct part is `Closing`'s.** On code without extended call forms
  logged extended runs are logged native runs (`evalLX_iff_evalL`). So on stores
  whose functions are direct (`XRecursion.StoreXFree`) the open modules agree
  (`wasmOpenX_eq`), and so do their closures (`close_wasmOpenX_eq`).

**Not here.** Divergence through the extended forms (`Shape.closeDL` on
`wasmOpenX`), and Core 3.0 adequacy of the extended rules.
-/

public section

namespace Silmaril.Wasm.Abstract.XClosing

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (wasmOShape OCall endOfFlow EvalL wasmOpen)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.XRecursion

variable {H : Type}

/-- **Closing the extended open module gives the closed extended outcomes.** -/
theorem close_wasmOpenX (a : Nat) (s : Store H) (vs : List Val) :
    Shape.close wasmOpenX a s vs =
      {y | ∃ s' fl, ClosedOutcomeX s a vs s' fl ∧ y = ([], endOfFlow fl s')} :=
  Silmaril.Proofs.Wasm.Abstract.XClosing.close_wasmOpenX a s vs

theorem evalLX_iff_evalL {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (hx : xFreeL es = true) {l : List (OCall H)} {r : Store H × Frame × Flow} :
    EvalLX s f stk es l r ↔ EvalL s f stk es l r :=
  Silmaril.Proofs.Wasm.Abstract.XClosing.evalLX_iff_evalL hx

/-- **On a direct store, the open modules agree.** -/
theorem wasmOpenX_eq {s : Store H} (hs : StoreXFree s) (a : Nat) (vs : List Val) :
    wasmOpenX a s vs = wasmOpen a s vs :=
  Silmaril.Proofs.Wasm.Abstract.XClosing.wasmOpenX_eq hs a vs

/-- **On a direct store, the closures agree.** -/
theorem close_wasmOpenX_eq {s : Store H} (hs : StoreXFree s) (a : Nat) (vs : List Val) :
    Shape.close wasmOpenX a s vs = Shape.close wasmOpen a s vs :=
  Silmaril.Proofs.Wasm.Abstract.XClosing.close_wasmOpenX_eq hs a vs

end Silmaril.Wasm.Abstract.XClosing
