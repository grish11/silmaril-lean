module

import Silmaril.Formats.Csv.NamedTable.Thms
meta import Silmaril.Formats.Csv.NamedTable.Defs

/-! Executable examples with a fixture codec for field bytes. -/

namespace Silmaril.Formats.Csv.NamedTable

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Relational.NamedTable (Packed importArrow importParquet)

private meta def Value (_ : Bool) := Field

private meta def codecs (k : Bool) : Typed.CellCodec (Value k) := ⟨some, some⟩

private meta def bytes (text : String) : Bytes := text.toUTF8.data.toList

private meta def schema : Typed.Schema Bool := ⟨1, fun _ => (bytes "x", false)⟩

private meta def wrongKind : Typed.Schema Bool := ⟨1, fun _ => (bytes "x", true)⟩

private meta def rows : Typed.Table schema Value := [fun _ => none, fun _ => some [], fun _ => none]

private meta def cells (table : Scan.Observation Field Value) : List (List (Option Field)) :=
  table.rows.map List.ofFn

private meta def db : Packed Nat Field Value := fun name =>
  if name = 0 then some ⟨schema, [fun _ => some (bytes "keep")]⟩ else none

private meta def input : Bytes := bytes "x\r\nN\r\nT\r\nN\r\n"

private meta def canonical : Bytes := bytes "\"x\"\r\n\"N\"\r\n\"T\"\r\n\"N\"\r\n"

#guard (importCsv db 1 schema schema codecs input).map
  (fun loaded => (Scan.observePacked loaded 1).map cells) = .ok (some [[none], [some []], [none]])

#guard (importCsv db 1 schema schema codecs input).map
  (fun loaded => (Scan.observePacked loaded 0).map cells) = .ok (some [[some (bytes "keep")]])

#guard (importCsv db 0 schema schema codecs input).map (fun _ => ()) = .error .nameConflict

#guard (importCsv db 1 schema wrongKind codecs input).map (fun _ => ()) = .error .schemaMismatch

#guard (importCsv db 1 schema schema codecs (bytes "y\r\nN\r\n")).map (fun _ => ()) =
  .error (.openError .headerMismatch)

#guard (importCsv db 1 schema schema codecs (bytes "x\r\nN\r\nX\r\n")).map (fun _ => ()) =
  .error (.openError (.invalidTag 0))

#guard (exportCsv db 1 codecs).map Prod.snd = .error .missingName

private meta def arrow : Events.EventStream Field Value Nat :=
  .ok ⟨schema, ⟨[AlignedColumns.ofRows (rows.take 1), AlignedColumns.ofRows (rows.drop 1)], .eos⟩⟩

private meta def parquet (fail : Bool) : Reader.OpenResult Nat Field Value Nat :=
  .ok ⟨schema, ⟨[0, 1], fun n => if n = 0 then .ok (rows.take 1)
    else if fail then .error 17 else .ok (rows.drop 1), fun _ => .ok ()⟩⟩

#guard (importArrow db 1 schema arrow).toOption.bind
  (fun loaded => ((exportCsv loaded 1 codecs).map Prod.snd).toOption) = some canonical

#guard (importParquet db 1 schema (parquet false)).toOption.bind
  (fun loaded => ((exportCsv loaded 1 codecs).map Prod.snd).toOption) = some canonical

#guard (importParquet db 1 schema (parquet true)).map (fun _ => ()) = .error (.readError 17)

#guard (eventsOfBytes schema codecs canonical).collect.map
  (fun observed => (cells observed.table, observed.termination)) =
    .ok ([[none], [some []], [none]], .eos)

private meta def zero : Typed.Schema Bool := ⟨0, fun i => i.elim0⟩
private meta def emptyRow : Scan.Row zero Value := fun i => i.elim0

private meta def zeroDb : Packed Nat Field Value := fun name =>
  if name = 0 then some ⟨zero, [emptyRow, emptyRow]⟩ else none

#guard (exportCsv zeroDb 0 codecs).map Prod.snd = .ok (bytes "\"\"\r\n\"\"\r\n\"\"\r\n")

#guard (importCsv db 1 zero zero codecs (bytes "\"\"\r\n\"\"\r\n\"\"\r\n")).map
  (fun loaded => (Scan.observePacked loaded 1).map Scan.Observation.rowCount) = .ok (some 2)

end Silmaril.Formats.Csv.NamedTable
