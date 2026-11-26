module

import Silmaril.Formats.Arrow.FromCsv.Stream.Thms
meta import Silmaril.Formats.Arrow.FromCsv.Stream.Defs
meta import Silmaril.Formats.Arrow.ToCsv.Fixture

/-! Complete stream readback and the boundary between adapter and writer errors. -/

namespace Silmaril.Formats.Arrow.FromCsv.Stream

open Silmaril.Formats.Relational.NamedTable (Packed)
open ToCsv (Cell)

private meta def utf8Fields : List Field := [⟨"café", true, .utf8⟩]

private meta def utf8Csv : Csv.Bytes :=
  "\"café\"\r\n\"T雪\"\r\n\"N\"\r\n\"T\"\r\n".toUTF8.data.toList

private meta def asciiFields : List Field := [⟨"n", true, .int32⟩, ⟨"text", true, .utf8⟩]

#guard ((emitCsvUtf8 {} utf8Fields utf8Csv).toOption.bind
    fun ipc => (readRows {} ipc).toOption).map (fun seen => (seen.fields, seen.batches)) =
  some (utf8Fields, [[[some (.utf8 "雪")], [none], [some (.utf8 "")]]])

#guard ((emitCsv {} [] "\"\"\r\n\"\"\r\n\"\"\r\n".toUTF8.data.toList).toOption.bind
    fun ipc => (readRows {} ipc).toOption).map (fun seen => (seen.fields, seen.batches)) =
  some ([], [[[], []]])

#guard (emitCsv {} asciiFields.reverse ToCsv.Fixture.csv.toList).map (fun _ => ()) =
  .error (.adapter (.csv .headerMismatch))

#guard (emitCsv {} [⟨"n", false, .int32⟩, ⟨"text", true, .utf8⟩] ToCsv.Fixture.csv.toList).map
  (fun _ => ()) = .error (.adapter .requiredNull)

#guard (emitCsvUtf8 {} utf8Fields [0xff]).map (fun _ => ()) = .error (.adapter (.csv .malformedWire))

#guard (emitNamed {} (fun (_ : Nat) => none : Packed Nat Csv.Field Cell) 7 utf8Fields).map
  (fun _ => ()) = .error (.adapter .missingName)

#guard (emitCsv { ipc := { batches := 0 } } asciiFields ToCsv.Fixture.csv.toList).map (fun _ => ()) =
  .error (.writer (.limit .batches))

#guard (emitCsv { totalRows := 3 } asciiFields ToCsv.Fixture.csv.toList).map (fun _ => ()) =
  .error (.writer (.limit .totalRows))

end Silmaril.Formats.Arrow.FromCsv.Stream
