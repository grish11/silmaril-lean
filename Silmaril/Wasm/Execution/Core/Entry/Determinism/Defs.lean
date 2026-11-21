module

public import Silmaril.Wasm.Execution.Core.Entry.Defs
public import Silmaril.Semantics.Operational.Determinism.Fuel.Defs
public import Silmaril.Wasm.SingleThreaded.Exec.Run
public import Silmaril.Wasm.Cfg.ProfileFree.Defs

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Entry

open Numerics Semantics.Operational SingleThreaded.Exec
open Intrinsic (Completion observeResult)

/-- Use the existing Core driver for steps at the profile/host justified by
its soundness argument. A failed driver step is only a finite result if the
existing result classifier recognizes it; otherwise the answer is unknown. -/
def driverDecision {H : Type} (head : HeadFn H) (source : Config H) : Decision (Config H) Completion :=
  match source.outcome? with
  | some result => .stop (.observed (observeResult result))
  | none => match step? head source with
    | some target => .move target
    | none => .stop .unknown

end Silmaril.Wasm.Execution.Core.Entry

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Semantics.Operational Validation Numerics

variable {H : Type} {context : Context} {world : World H context} {locals results : List IntType}

/-- Reuse the intrinsic normalizing machine, not raw administrative step uniqueness. -/
def normalDecision (state : State world locals results) : Decision (State world locals results) Completion :=
  match state.step? with
  | some next => .move next
  | none => match state.result? with
    | some result => .stop (.observed (observeResult result))
    | none => .stop .unknown

end Silmaril.Wasm.Execution.Core.Intrinsic
