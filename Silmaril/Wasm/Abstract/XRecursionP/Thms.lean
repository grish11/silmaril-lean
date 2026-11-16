module

public import Silmaril.Wasm.Abstract.XRecursionP.Defs

/-!
# The closed call relation with pending tail calls: theorems

`closedCallXP_fixpoint`: the closure answers a call exactly by a run of the callee's body against
the closure itself, its pending tail call (if any) answered when its frame is left.
-/

public section

namespace Silmaril.Wasm.Abstract.XRecursionP

open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallXP

variable {H : Type}

theorem closedCallXP_fixpoint : (closedCallXP : CallRel H) = bodyCallXP closedCallXP :=
  (OrderHom.map_lfp bodyCallXPOp).symm

end Silmaril.Wasm.Abstract.XRecursionP
