module

public import Silmaril.Formats.Arrow.DateStream.Narrow.Defs
import Silmaril.Proofs.Formats.Arrow.DateStream.Narrow

public section

namespace Silmaril.Formats.Arrow.DateStream.Narrow

/-- Success recovers exactly the source field and the nested nullable slot lists.
Each inner list is one source batch, including an empty batch. -/
theorem read_ok_iff (limits : Limits) (input : KBytes) (output : Stream) :
    read limits input = .ok output ↔
      DateStream.read limits input =
        .ok ⟨⟨output.name, output.nullable, .millisecond⟩, civilBatches output⟩ :=
  Proofs.Formats.Arrow.DateStream.Narrow.read_ok_iff limits input output

/-- The first unrepresentable day is identified after its representable batch
and slot prefixes, with zero-based indices and the exact signed epoch day. -/
theorem read_outOfRange_iff (limits : Limits) (input : KBytes)
    (batch slot : Nat) (day : Int) :
    read limits input = .error (.outOfRange batch slot day) ↔
      ∃ source, DateStream.read limits input = .ok source ∧ source.field.unit = .millisecond ∧
        FirstOutOfRange source.batches batch slot day :=
  Proofs.Formats.Arrow.DateStream.Narrow.read_outOfRange_iff limits input batch slot day

/-- Any IPC-stage failure takes precedence over narrowing. -/
theorem read_of_reader_error {limits : Limits} {input : KBytes} {cause : DateStream.Error}
    (failed : DateStream.read limits input = .error cause) :
    read limits input = .error (.reader cause) := by
  simp [read, failed, Except.mapError, Bind.bind, Except.bind]

/-- DateStream certifies the civil dates before attempting the Int32 check. -/
theorem read_ne_invalidCivil (limits : Limits) (input : KBytes) (batch slot : Nat) :
    read limits input ≠ .error (.invalidCivil batch slot) :=
  Proofs.Formats.Arrow.DateStream.Narrow.read_ne_invalidCivil limits input batch slot

end Silmaril.Formats.Arrow.DateStream.Narrow
