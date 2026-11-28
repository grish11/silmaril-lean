module

public import Silmaril.Formats.Arrow.Layout.Defs
import Silmaril.Prelude.Bytes.Thms
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow

open Silmaril.Formats.Arrow

theorem BuffersFit.mem_fits {bodyLength previousEnd : Nat} {buffers : List Buffer}
    (ordered : BuffersFit bodyLength previousEnd buffers) {buffer : Buffer}
    (member : buffer ∈ buffers) : buffer.Fits bodyLength previousEnd := by
  induction buffers generalizing previousEnd with
  | nil => simp at member
  | cons head tail ih =>
    obtain ⟨headFits, tailFit⟩ := ordered
    rcases List.mem_cons.mp member with rfl | inTail
    · exact headFits
    · obtain ⟨lower, aligned, upper⟩ := ih tailFit inTail
      exact ⟨by have := headFits.1; omega, aligned, upper⟩

theorem BatchFrame.buffer_exact {fields : List Field} (frame : BatchFrame fields)
    (wf : frame.body.wf = true) {buffer : Buffer} (member : buffer ∈ frame.metadata.buffers) :
    let bytes := frame.body.slice buffer.offset buffer.length
    bytes.len = buffer.length ∧
      bytes.toList = (frame.body.toList.drop buffer.offset).take buffer.length := by
  have fits := BuffersFit.mem_fits frame.layout.2.2.2 member
  exact ⟨KBytes.len_slice _ _ _, KBytes.toList_slice _ _ _ wf fits.2.2⟩

theorem validateBatch_iff (fields : List Field) (batch : RecordBatch) (body : KBytes) :
    (∃ frame, validateBatch fields batch body = .ok frame) ↔ batch.Fits fields body.len := by
  unfold validateBatch
  split <;> simp_all

end Silmaril.Proofs.Formats.Arrow
