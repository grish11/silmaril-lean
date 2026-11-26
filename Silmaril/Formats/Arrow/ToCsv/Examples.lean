module

import Silmaril.Formats.Arrow.ToCsv.Thms
meta import Silmaril.Formats.Arrow.ToCsv.Defs
meta import Silmaril.Formats.Arrow.ToCsv.Fixture

/-! Executable regressions against pinned PyArrow and CPython csv observations. -/

namespace Silmaril.Formats.Arrow.ToCsv

open Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (Packed)

private meta def fields : List Field := [⟨"n", true, .int32⟩, ⟨"text", true, .utf8⟩]

private meta def expected : List Row :=
  [[some (.int32 (-2147483648)), some (.utf8 "a,\"b\"\r\nc")],
    [none, some (.utf8 "")],
    [some (.int32 2147483647), none],
    [some (.int32 0), some (.utf8 "N")]]

private meta def db : Packed Nat Csv.Field Cell := fun name =>
  if name = 0 then some ⟨schemaOf fields, []⟩ else none

#guard (readRows {} Fixture.ipc).map (fun observed => (observed.fields, observed.batches.flatten)) =
  .ok (fields, expected)

#guard (convert db 1 (schemaOf fields) {} Fixture.ipc).map Prod.snd = .ok Fixture.csv.toList

#guard (Csv.Typed.decode (schemaOf fields) codecs Fixture.csv.toList).map (List.map (eraseRow fields)) =
  .ok expected

#guard (importIpc db 1 (schemaOf fields) {} Fixture.ipc).map
  (fun loaded => (Scan.observePacked loaded 1).map Scan.Observation.rowCount) = .ok (some 4)

#guard (importIpc db 1 (schemaOf fields) {} Fixture.ipc).map
  (fun loaded => (Scan.observePacked loaded 0).map Scan.Observation.rowCount) = .ok (some 0)

#guard (convert db 1 (schemaOf fields) {} (Fixture.ipc.slice 0 (Fixture.ipc.len - 8))).map Prod.snd =
  .error (.input (.openError (.ipc (.malformed .truncated))))

#guard (convert db 1 (schemaOf fields) {} (Fixture.ipc ++ .leaf 1 0)).map Prod.snd =
  .error (.input (.openError (.ipc (.malformed .trailingBytes))))

#guard (convert db 1 (schemaOf fields.reverse) {} Fixture.ipc).map Prod.snd =
  .error (.input .schemaMismatch)

#guard (convert db 0 (schemaOf fields) {} Fixture.ipc).map Prod.snd = .error (.input .nameConflict)

#guard (typedRow fields [some (.utf8 "not an int"), none]).map (fun _ => ()) =
  .error .cellKind

#guard (typedRow fields [none]).map (fun _ => ()) = .error .rowWidth

#guard (typedRow [⟨"required", false, .int32⟩] [none]).map (fun _ => ()) =
  .error .requiredNull

end Silmaril.Formats.Arrow.ToCsv
