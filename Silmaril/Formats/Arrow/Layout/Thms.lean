module

public import Silmaril.Formats.Arrow.Layout.Defs
import Silmaril.Proofs.Formats.Arrow.Layout

@[expose] public section

namespace Silmaril.Formats.Arrow

/-- Every descriptor in an ordered layout is aligned and bounded by the body. -/
theorem BuffersFit.mem_fits {bodyLength previousEnd : Nat} {buffers : List Buffer}
    (ordered : BuffersFit bodyLength previousEnd buffers) {buffer : Buffer}
    (member : buffer ∈ buffers) : buffer.Fits bodyLength previousEnd :=
  Proofs.Formats.Arrow.BuffersFit.mem_fits ordered member

/-- A descriptor in a checked batch selects the exact byte window of that buffer. -/
theorem BatchFrame.buffer_exact {fields : List Field} (frame : BatchFrame fields)
    (wf : frame.body.wf = true) {buffer : Buffer} (member : buffer ∈ frame.metadata.buffers) :
    let bytes := frame.body.slice buffer.offset buffer.length
    bytes.len = buffer.length ∧
      bytes.toList = (frame.body.toList.drop buffer.offset).take buffer.length :=
  Proofs.Formats.Arrow.BatchFrame.buffer_exact frame wf member

/-- The descriptor validator succeeds exactly for the declared layout relation. -/
theorem validateBatch_iff (fields : List Field) (batch : RecordBatch) (body : KBytes) :
    (∃ frame, validateBatch fields batch body = .ok frame) ↔ batch.Fits fields body.len :=
  Proofs.Formats.Arrow.validateBatch_iff fields batch body

end Silmaril.Formats.Arrow
