module

import Silmaril.Formats.Arrow.ToCsv.Utf8.Thms
import Silmaril.Formats.Arrow.FromCsv.Stream.Thms
meta import Silmaril.Formats.Arrow.ToCsv.Utf8.Defs
meta import Silmaril.Formats.Arrow.FromCsv.Stream.Defs

/-! Exercise complete IPC input, UTF-8 encoding, and full readback. -/

namespace Silmaril.Formats.Arrow.ToCsv.Utf8

open Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (Packed)

private meta def fields : List Field := [⟨"café", true, .utf8⟩]

private meta def db : Packed Nat Csv.Field Cell := fun name =>
  if name = 0 then some ⟨schemaOf fields, []⟩ else none

private meta def batch (values : List (Option String)) : Writer.BatchInput :=
  ⟨values.length, [⟨"café", true, .utf8 values⟩]⟩

private meta def ipc : Except Error KBytes :=
  StreamWriter.emit {} fields [batch [some "é", none], batch [], batch [some "", some "雪"]]

private meta def expectedCsv : Csv.Bytes :=
  "\"café\"\r\n\"Té\"\r\n\"N\"\r\n\"T\"\r\n\"T雪\"\r\n".toUTF8.data.toList

#guard (ipc.toOption.bind fun wire => (convert db 1 (schemaOf fields) {} wire).toOption.map
    fun (loaded, _, csv) =>
      ((Scan.observePacked loaded 1).map Scan.Observation.rowCount,
       (Scan.observePacked loaded 0).map Scan.Observation.rowCount, csv)) =
  some (some 4, some 0, expectedCsv)

#guard (ipc.toOption.map fun wire =>
    (convert db 1 (schemaOf fields) {} (wire.slice 0 (wire.len - 1))).map (fun _ => ())) =
  some (.error (.input (.openError (.ipc (.malformed .truncated)))))

#guard (ipc.toOption.map fun wire =>
    (convert db 1 (schemaOf fields) {} (wire ++ .leaf 1 0)).map (fun _ => ())) =
  some (.error (.input (.openError (.ipc (.malformed .trailingBytes)))))

#guard ((StreamWriter.emit {} fields [batch [some "é\t雪"]]).toOption.map fun wire =>
    (convert db 1 (schemaOf fields) {} wire).map (fun _ => ())) =
  some (.error (.output (.encodeError .unrepresentableWire)))

#guard (ipc.toOption.map fun wire => (convert db 0 (schemaOf fields) {} wire).map (fun _ => ())) =
  some (.error (.input .nameConflict))

#guard (ipc.toOption.map fun wire => (convert db 1 (schemaOf []) {} wire).map (fun _ => ())) =
  some (.error (.input .schemaMismatch))

#guard ((FromCsv.Stream.emitCsvUtf8 {} fields expectedCsv).toOption.bind fun output =>
    (readRows {} output).toOption.map fun read => (read.fields, read.batches)) =
  some (fields, [[[some (.utf8 "é")], [none], [some (.utf8 "")], [some (.utf8 "雪")]]])

private meta def zeroCsv : Csv.Bytes := "\"\"\r\n\"\"\r\n\"\"\r\n".toUTF8.data.toList

#guard ((FromCsv.Stream.emitCsvUtf8 {} [] zeroCsv).toOption.bind fun output =>
    (convert db 1 (schemaOf []) {} output).toOption.map fun (loaded, _, csv) =>
      ((Scan.observePacked loaded 1).map Scan.Observation.rowCount, csv)) =
  some (some 2, zeroCsv)

end Silmaril.Formats.Arrow.ToCsv.Utf8
