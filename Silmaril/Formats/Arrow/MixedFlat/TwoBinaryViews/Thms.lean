module

public import Silmaril.Formats.Arrow.MixedFlat.TwoBinaryViews.Defs
public import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Thms

public section

namespace Silmaril.Formats.Arrow.MixedFlat.TwoBinaryViews

export OrderedWriter (compile_binary_wire record_wire)

/-- The two-view profile reads back the declared fields and every explicit
batch through exact EOS. -/
theorem emit_readback {limits : MixedFlat.Limits} {fields : List Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire) :
    ∃ decoded, Stream.read limits wire = .ok decoded ∧ decoded.fields = fields ∧
      decoded.batches.map StreamWriter.observeBatch = batches.map BatchInput.observe ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame limits.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire limits wire decoded.fields limits.observation.ipc.batches 0 start decoded.batches :=
  OrderedWriter.emit_readback written

end Silmaril.Formats.Arrow.MixedFlat.TwoBinaryViews
