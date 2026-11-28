module

public import Silmaril.Formats.Arrow.DateStream.ToCsv.Defs

/-! # Typed Date32 CSV export observing rows across all IPC batches -/

@[expose] public section

namespace Silmaril.Formats.Arrow.DateStream.ToCsv.RowObservational

/-- Consume the admitted stream through EOS, then recover the exact signed
slots in order. Schema-only streams and empty batches contribute no rows. -/
def readRows (ipc : Limits) (name : String) (nullable : Bool) (input : KBytes) :
    Except Error Writer.Column := do
  let source ← (DateStream.read ipc input).mapError .reader
  if source.field ≠ ⟨name, nullable, .day⟩ then throw (.descriptor source.field)
  let some slots := Internal.recover source.batches.flatten | .error .unrepresentableDay
  return slots

/-- Export one canonical typed CSV table. Its row cap applies to the total
across all admitted IPC batches, and its byte cap applies to the canonical CSV. -/
def exportRows (ipc : Limits) (csv : FromCsv.CsvLimits) (name : String) (nullable : Bool)
    (input : KBytes) : Except Error Csv.Bytes := do
  let slots ← readRows ipc name nullable input
  Internal.encodeColumn csv name nullable slots

end Silmaril.Formats.Arrow.DateStream.ToCsv.RowObservational
