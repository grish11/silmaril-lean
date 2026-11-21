module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Defs

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Validation

/-- Failure of Core configuration typing at the chosen result interface.
This adapter policy is not a reduction rule of Core. -/
def typingUB {H : Type} (types : List CValType) (config : Config H) : Prop :=
  ¬ ConfigOk config types

end Silmaril.Wasm.Execution.Core.Intrinsic
