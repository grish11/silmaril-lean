module

public import Silmaril.Formats.Arrow.Framing.Incremental.Defs
import Silmaril.Proofs.Formats.Arrow.Framing.Incremental.Feed

public section

namespace Silmaril.Formats.Arrow.Framing.Incremental

/-- Each request retains exactly the wanted prefix and returns the untouched
suffix, independent of the rope shapes used for incoming bytes. -/
theorem buffer_feed {capacity : Nat} (buffer : Buffer capacity) (chunk : KBytes)
    (valid : chunk.wf = true) :
    let filled := buffer.feed chunk valid
    let bytes := buffer.bytes.toList ++ chunk.toList
    filled.buffered.bytes.toList = bytes.take capacity ∧
      filled.rest.toList = bytes.drop capacity ∧ filled.rest.wf = true :=
  Proofs.Formats.Arrow.Framing.Incremental.buffer_feed buffer chunk valid

/-- Start at an absolute offset in the immutable reference. -/
theorem start_refines {limits : Limits} {input : KBytes} {offset : Nat} (bounded : offset ≤ input.len) :
    (start offset).InCarrier limits input :=
  Proofs.Formats.Arrow.Framing.Incremental.start_refines bounded

/-- A successful feed preserves the immutable reference for the next ordered
chunk or returned suffix. Any emitted frame agrees with the carrier decoders. -/
theorem feed_refines {limits : Limits} {input : KBytes} {state : State} {chunk : KBytes}
    {result : Progress} (wf : input.wf = true) (held : state.InCarrier limits input)
    (incoming : Window input state.position chunk)
    (fed : feed limits state chunk = .ok result) :
    result.InCarrier limits input state chunk :=
  Proofs.Formats.Arrow.Framing.Incremental.feed_refines wf held incoming fed

/-- After all bytes have been supplied, successful finalization identifies
the original EOS at the exact end of the immutable reference. -/
theorem finish_refines {limits : Limits} {input : KBytes} {state : State} {last : Nat}
    (held : state.InCarrier limits input) (exhausted : state.position = input.len)
    (finished : finish state = .ok last) :
    last = input.len ∧ ∃ offset, offset + 8 = last ∧ readEnvelope limits input offset = .ok .eos :=
  Proofs.Formats.Arrow.Framing.Incremental.finish_refines held exhausted finished

/-- A later nonempty valid chunk after EOS fails at the first tail byte. -/
theorem feed_ended_tail {limits : Limits} {offset : Nat} {chunk : KBytes}
    (valid : chunk.wf = true) (nonempty : chunk.len ≠ 0) :
    feed limits (.ended offset) chunk = .error ⟨.tail, offset, .malformed .trailingBytes⟩ := by
  simp [feed, valid, nonempty]

end Silmaril.Formats.Arrow.Framing.Incremental
