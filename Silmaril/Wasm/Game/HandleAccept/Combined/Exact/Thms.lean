module

public import Silmaril.Wasm.Game.HandleAccept.Combined.Thms
public import Silmaril.Wasm.Verify.Refute.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Combined.Exact

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Combined

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Accept.Handle
open Silmaril.Wasm.Numerics (Profile)

/-- `readBack` accepts precisely the singleton word lists for any sentinel. The profile must
admit the reference interpreter's deterministic steps and the write/accept policy must not
admit undefined behaviour. -/
theorem readBack_exact {P : Profile}
    (hP : ∀ before after : Config Nat,
      Step (profile refOracle) Det.noHost before after → Step P Det.noHost before after)
    {pol : Policy (BitVec 32)} (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    moduleCombLang P readBack readBackIx pol = singleL :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Combined.readBack_exact hP hw ha

end Silmaril.Wasm.Game.HandleAccept.Combined
