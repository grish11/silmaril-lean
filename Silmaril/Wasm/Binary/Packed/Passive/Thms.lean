module

public import Silmaril.Wasm.Binary.Packed.Passive.Defs
import Silmaril.Proofs.Wasm.Binary.Packed.Passive

public section

namespace Silmaril.Wasm.Binary.Packed

/-- Transfer a checked packed decode of a single passive data segment to the full Core decoder.
The source starts at byte zero and is consumed through EOF; no other section is permitted. -/
theorem PassivePlan.Verified.sound {plan : PassivePlan} {source payload : KBytes} {wf : source.wf = true}
    (payloadWf : payload.wf = true) (checked : plan.Verified source wf payload) :
    Core.decode? source.toByteArray = some { data := [⟨payload.toByteArray, .passive⟩] } :=
  Proofs.Wasm.Binary.Packed.Passive.sound payloadWf checked

end Silmaril.Wasm.Binary.Packed
