module

public import Silmaril.Formats.Arrow.BinaryView.Defs
import Silmaril.Proofs.Formats.Arrow.BinaryView.Read

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView

/-- A read succeeds exactly when the slot and its selected payload meet the
wire, range and budget conditions. -/
theorem readBinary_iff (buffers : Buffers) (index maxValueBytes : Nat) (value : KBytes) :
    readBinary buffers index maxValueBytes = .ok value ↔ Wire buffers index maxValueBytes value :=
  Proofs.Formats.Arrow.BinaryView.readBinary_iff buffers index maxValueBytes value

theorem readBinary_extent {buffers : Buffers} {index maxValueBytes : Nat} {value : KBytes}
    (read : readBinary buffers index maxValueBytes = .ok value) :
    value.wf = true ∧ value.len = buffers.views.read (16 * index) 4 ∧ value.len ≤ maxValueBytes :=
  Proofs.Formats.Arrow.BinaryView.readBinary_extent read

/-- A Utf8View additionally requires the exact payload to decode as UTF-8. -/
theorem readUtf8_iff (buffers : Buffers) (index maxValueBytes : Nat) (text : String) :
    readUtf8 buffers index maxValueBytes = .ok text ↔
      ∃ bytes, Wire buffers index maxValueBytes bytes ∧
        String.fromUTF8? bytes.toByteArray = some text :=
  Proofs.Formats.Arrow.BinaryView.readUtf8_iff buffers index maxValueBytes text

end Silmaril.Formats.Arrow.BinaryView
