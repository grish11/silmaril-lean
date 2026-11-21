module

public import Silmaril.Wasm.Binary.Packed.Bounded.Defs
import Silmaril.Proofs.Wasm.Binary.Packed.Bounded

public section

namespace Silmaril.Wasm.Binary.Packed.Bounded

/-- A successful bounded computation gives the reference decoder's result on the same
bytes, including the final check that all input has been consumed. -/
theorem decode_sound {source : KBytes} {wf : source.wf = true} {codeEnds : Option (List Nat)}
    {decoded : Wasm.Module}
    (checked : decode? source wf codeEnds = some decoded) :
    Core.decode? source.toByteArray = some decoded :=
  Proofs.Wasm.Binary.Packed.Bounded.sound checked

end Silmaril.Wasm.Binary.Packed.Bounded
