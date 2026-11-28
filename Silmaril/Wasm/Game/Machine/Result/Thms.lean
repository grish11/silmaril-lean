module

public import Silmaril.Wasm.Game.Machine.Defs
import Silmaril.Proofs.Wasm.Game.Machine.Basic

public section

namespace Silmaril.Wasm.Game

open Silmaril.Wasm.Execution.Core (Result Store)
open Silmaril.Wasm.SingleThreaded (Thread)

/-- The terminal code of a thread determines its Core result. -/
theorem ResultAt.unique {s : Store Nat} {t : Thread} {r r' : Result}
    (h : ResultAt s t r) (h' : ResultAt s t r') : r = r' :=
  Silmaril.Proofs.Wasm.Game.result_toAdmin_injective (h.symm.trans h')

end Silmaril.Wasm.Game
