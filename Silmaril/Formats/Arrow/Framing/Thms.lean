module

public import Silmaril.Formats.Arrow.Framing.Defs
import Silmaril.Proofs.Formats.Arrow.Framing

@[expose] public section

namespace Silmaril.Formats.Arrow

/-- Framing is sound and complete for the bounded modern prefix relation. -/
theorem readEnvelope_iff (limits : Limits) (input : KBytes) (offset : Nat)
    (envelope : Envelope) (wf : input.wf = true) :
    readEnvelope limits input offset = .ok envelope ↔
      EnvelopeWire limits input.toList offset envelope :=
  Proofs.Formats.Arrow.readEnvelope_iff limits input offset envelope wf

/-- An accepted metadata prefix covers precisely its declared padded span. -/
theorem metadata_exact {limits : Limits} {input : KBytes} {offset size : Nat}
    (wf : input.wf = true) (read : readEnvelope limits input offset = .ok (.metadata size)) :
    (input.slice (offset + 8) size).toList = (input.toList.drop (offset + 8)).take size :=
  Proofs.Formats.Arrow.metadata_exact wf read

theorem readBody_iff (limits : Limits) (input : KBytes) (offset size : Nat) (body : KBytes) :
    readBody limits input offset size = .ok body ↔
      offset % 8 = 0 ∧ size % 8 = 0 ∧ size ≤ limits.bodyBytes ∧
        offset + size ≤ input.len ∧ body = input.slice offset size :=
  Proofs.Formats.Arrow.readBody_iff limits input offset size body

/-- The body slice has the declared length and contains the original bytes. -/
theorem body_exact {limits : Limits} {input : KBytes} {offset size : Nat} {body : KBytes}
    (wf : input.wf = true) (read : readBody limits input offset size = .ok body) :
    body.len = size ∧ body.toList = (input.toList.drop offset).take size :=
  Proofs.Formats.Arrow.body_exact wf read

/-- Successful prefix observations are independent of the kernel byte tree shape. -/
theorem readEnvelope_rechunk {input other : KBytes} (wf : input.wf = true)
    (otherWf : other.wf = true) (same : input.toList = other.toList)
    (limits : Limits) (offset : Nat) (envelope : Envelope) :
    readEnvelope limits input offset = .ok envelope ↔
      readEnvelope limits other offset = .ok envelope := by
  rw [readEnvelope_iff _ _ _ _ wf, readEnvelope_iff _ _ _ _ otherWf, same]

end Silmaril.Formats.Arrow
