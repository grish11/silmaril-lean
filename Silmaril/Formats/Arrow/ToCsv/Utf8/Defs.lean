module

public import Silmaril.Formats.Arrow.CsvUtf8.Defs
public import Silmaril.Formats.Csv.NamedTable.Utf8.Defs

/-! Checked Arrow IPC byte import followed by export through the named UTF-8 CSV API. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.ToCsv.Utf8

open Silmaril.Formats.Relational.NamedTable (Packed)

/-- Import only after complete IPC observation and explicit EOS. Return the
updated database together with the exported schema and bytes only on success. -/
def convert {Name : Type} [DecidableEq Name] (db : Packed Name Csv.Field Cell)
    (name : Name) (expected : Csv.Typed.Schema Kind) (limits : ObservationLimits) (input : KBytes) :
    Except ConvertError (Packed Name Csv.Field Cell × Csv.Typed.Schema Kind × Csv.Bytes) := do
  let loaded ← (importIpc db name expected limits input).mapError ConvertError.input
  let output ← (Csv.NamedTable.Utf8.exportCsv loaded name CsvUtf8.codecs).mapError ConvertError.output
  return (loaded, output)

end Silmaril.Formats.Arrow.ToCsv.Utf8
