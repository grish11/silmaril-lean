module

public import Silmaril.Formats.Arrow.ToCsv.Defs
public import Silmaril.Formats.Csv.Typed.Utf8.Defs

/-! Cell codecs for the flat Arrow profile at the typed UTF-8 CSV boundary. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.CsvUtf8

open ToCsv (Kind Cell)

def codecs : (kind : Kind) → Csv.Typed.CellCodec (Cell kind)
  | (.int32, _) => Csv.Typed.Codecs.int32
  | (.utf8, _) => Csv.Typed.Utf8.string

end Silmaril.Formats.Arrow.CsvUtf8
