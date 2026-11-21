module

public import Silmaril.Wasm.Binary.Packed.Passive.Defs
import Silmaril.Proofs.Wasm.Binary.Packed.Passive

public section

namespace Silmaril.Wasm.Binary.Packed

/-- Decoder assembly for exactly one passive segment. Both packed certificates and
symbolic serializers can establish these same Core reader facts. -/
theorem decodePassive_of_reads {bytes payload : ByteArray} {start afterCount afterMode payloadStart : Nat}
    (header : Core.Decode.readHeader.run ⟨bytes, 0⟩ = .ok ((), ⟨bytes, 8⟩))
    (identifier : Core.Decode.readByte.run ⟨bytes, 8⟩ = .ok (11, ⟨bytes, 9⟩))
    (present : 8 < bytes.size)
    (size : (Core.Decode.readU 32).run ⟨bytes, 9⟩ = .ok (bytes.size - start, ⟨bytes, start⟩))
    (count : (Core.Decode.readU 32).run ⟨bytes, start⟩ = .ok (1, ⟨bytes, afterCount⟩))
    (countFits : afterCount < bytes.size)
    (mode : (Core.Decode.readU 32).run ⟨bytes, afterCount⟩ = .ok (1, ⟨bytes, afterMode⟩))
    (length : (Core.Decode.readU 32).run ⟨bytes, afterMode⟩ = .ok (payload.size, ⟨bytes, payloadStart⟩))
    (endsAt : payloadStart + payload.size = bytes.size)
    (body : (Core.Decode.readBytes payload.size).run ⟨bytes, payloadStart⟩ = .ok (payload, ⟨bytes, bytes.size⟩)) :
    Core.decode? bytes = some { data := [⟨payload, .passive⟩] } :=
  Proofs.Wasm.Binary.Packed.Passive.decode_of_reads header identifier present size count countFits mode
    length endsAt body

/-- Transfer a checked packed decode of a single passive data segment to the full Core decoder.
The source starts at byte zero and is consumed through EOF; no other section is permitted. -/
theorem PassivePlan.Verified.sound {plan : PassivePlan} {source payload : KBytes} {wf : source.wf = true}
    (payloadWf : payload.wf = true) (checked : plan.Verified source wf payload) :
    Core.decode? source.toByteArray = some { data := [⟨payload.toByteArray, .passive⟩] } :=
  Proofs.Wasm.Binary.Packed.Passive.sound payloadWf checked

end Silmaril.Wasm.Binary.Packed
