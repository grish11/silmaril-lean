module

import Silmaril.Formats.Arrow.FromCsv.Thms
meta import Silmaril.Formats.Arrow.FromCsv.Defs
meta import Silmaril.Formats.Arrow.ToCsv.Fixture

/-! Exercise the CSV and named-table inputs through the physical writer and reader. -/

namespace Silmaril.Formats.Arrow.FromCsv

open Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (Packed)
open ToCsv (Cell schemaOf)

private meta def fields : List Field := [⟨"n", true, .int32⟩, ⟨"text", true, .utf8⟩]

private meta def expected : List Row :=
  [[some (.int32 (-2147483648)), some (.utf8 "a,\"b\"\r\nc")],
    [none, some (.utf8 "")],
    [some (.int32 2147483647), none],
    [some (.int32 0), some (.utf8 "N")]]

private meta def emitAndRead (adapted : Except AdapterError Writer.BatchInput) :
    Option (List Field × Nat × List Row) := do
  let input ← adapted.toOption
  let frame ← (Writer.emitBatch {} input).toOption
  let decoded ← (decodeBatch {} frame).toOption
  return (input.fields, frame.metadata.rowCount, decoded)

#guard emitAndRead (ofCsv fields ToCsv.Fixture.csv.toList) = some (fields, 4, expected)

#guard emitAndRead (ofRows fields []) = some (fields, 0, [])

#guard (ofCsv [⟨"n", false, .int32⟩, ⟨"text", true, .utf8⟩] ToCsv.Fixture.csv.toList).map
  (fun _ => ()) = .error .requiredNull

#guard (ofCsv fields.reverse ToCsv.Fixture.csv.toList).map (fun _ => ()) = .error (.csv .headerMismatch)

#guard emitAndRead (ofCsv [] "\"\"\r\n\"\"\r\n\"\"\r\n".toUTF8.data.toList) = some ([], 2, [[], []])

private meta def unicodeFields : List Field := [⟨"café", true, .utf8⟩]

private meta def unicodeDb : Packed Nat Csv.Field Cell := fun name =>
  if name = 7 then do
    let rows ← ([[some (.utf8 "λ")], [none], [some (.utf8 "λ")]].mapM
      (ToCsv.typedRow unicodeFields)).toOption
    return ⟨schemaOf unicodeFields, rows⟩
  else none

#guard emitAndRead (ofNamed unicodeDb 7 unicodeFields) =
  some (unicodeFields, 3, [[some (.utf8 "λ")], [none], [some (.utf8 "λ")]])

#guard (ofNamed unicodeDb 9 unicodeFields).map (fun _ => ()) = .error .missingName

#guard (ofNamed unicodeDb 7 [⟨"cafe", true, .utf8⟩]).map (fun _ => ()) = .error .schemaMismatch

end Silmaril.Formats.Arrow.FromCsv
