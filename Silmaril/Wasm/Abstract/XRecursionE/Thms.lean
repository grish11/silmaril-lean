module

public import Silmaril.Wasm.Abstract.XRecursionE.Defs
import Silmaril.Proofs.Wasm.Abstract.XRecursionE.Basic

/-!
# The closed call relation with exceptions: theorems

`closedCallXE_fixpoint`: the closure answers a call exactly by a run of the callee's body in
`EvalOXE` against the closure itself. `closedCallXE_funcs`: its answers keep the store's
functions.
-/

public section

namespace Silmaril.Wasm.Abstract.XRecursionE

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)

variable {H : Type}

/-- **The closure is a fixpoint.** -/
theorem closedCallXE_fixpoint : (closedCallXE : CallRel H) = bodyCallXE closedCallXE :=
  Silmaril.Proofs.Wasm.Abstract.XRecursionE.closedCallXE_eq_bodyCallXE

/-- The closure keeps the store's functions. -/
theorem closedCallXE_funcs {s : Store H} {a : Nat} {args : List Val} {out : Store H × Binaryen.Flow}
    (h : closedCallXE s a args out) : out.1.funcs = s.funcs :=
  Silmaril.Proofs.Wasm.Abstract.XRecursionE.closedCallXE_funcs s a args out h

end Silmaril.Wasm.Abstract.XRecursionE
