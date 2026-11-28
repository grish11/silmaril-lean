module

import Silmaril.Formats.Csv.EventStream.Thms
meta import Silmaril.Formats.Csv.EventStream.Defs

/-! Executable multi-batch conversions and errors at the typed event boundary. -/

namespace Silmaril.Formats.Csv.EventStream

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Relational.NamedTable (Packed)

private inductive SourceError where
  | openFailure
  | lateRead
  | closeFailure
  deriving DecidableEq

private meta def Value (_ : Bool) := String

private meta def codecs (k : Bool) : Typed.CellCodec (Value k) := Typed.Utf8.string

private meta def bytes (text : String) : Bytes := text.toUTF8.data.toList

private meta def schema : Typed.Schema Bool := ⟨1, fun _ => (bytes "都市", false)⟩

private meta def wrongKind : Typed.Schema Bool := ⟨1, fun _ => (bytes "都市", true)⟩

private meta def first : Typed.Table schema Value := [fun _ => none, fun _ => some ""]

private meta def last : Typed.Table schema Value := [fun _ => some "N", fun _ => some "東京,🙂\"\r\n"]

private meta def db : Packed Nat Field Value := fun name =>
  if name = 0 then some ⟨schema, [fun _ => some "保持"]⟩ else none

private meta def observed (db : Packed Nat Field Value) (name : Nat) :
    Option (List (List (Option String))) :=
  (Scan.observePacked db name).map fun table => table.rows.map List.ofFn

private meta def stream (termination : Events.Termination SourceError) :
    Events.EventStream Field Value SourceError :=
  .ok ⟨schema, ⟨[AlignedColumns.ofRows first, AlignedColumns.ofRows [],
    AlignedColumns.ofRows last], termination⟩⟩

private meta def output : Bytes :=
  bytes "\"都市\"\r\n\"N\"\r\n\"T\"\r\n\"TN\"\r\n\"T東京,🙂\"\"\r\n\"\r\n"

private meta def cells : List (List (Option String)) :=
  [[none], [some ""], [some "N"], [some "東京,🙂\"\r\n"]]

#guard (convert db 1 schema codecs (stream .eos)).map Result.wire = .ok output
#guard (convert db 1 schema codecs (stream .eos)).map (fun result => List.ofFn result.schema.kind) =
  .ok [(bytes "都市", false)]
#guard (convert db 1 schema codecs (stream .eos)).map (fun result => observed result.db 1) = .ok (some cells)
#guard (convert db 1 schema codecs (stream .eos)).map (fun result => observed result.db 0) =
  .ok (some [[some "保持"]])

#guard (convert db 1 schema codecs (.error SourceError.openFailure)).map Result.wire =
  .error (.input (.openError .openFailure))
#guard (convert db 0 schema codecs (.error SourceError.openFailure)).map Result.wire =
  .error (.input .nameConflict)
#guard (convert db 1 schema codecs (stream (.readError .lateRead))).map Result.wire =
  .error (.input (.readError .lateRead))
#guard (convert db 1 schema codecs (stream .closed)).map Result.wire = .error (.input .closed)
#guard (convert db 1 schema codecs (stream (.closeError .closeFailure))).map Result.wire =
  .error (.input (.closeError .closeFailure))
#guard (convert db 1 wrongKind codecs (stream .eos)).map Result.wire = .error (.input .schemaMismatch)

private meta def unrepresentable : Events.EventStream Field Value SourceError :=
  .ok ⟨schema, ⟨[AlignedColumns.ofRows first,
    AlignedColumns.ofRows [fun _ => some "東京\t"]], .eos⟩⟩

#guard (convert db 1 schema codecs unrepresentable).map Result.wire =
  .error (.output (.encodeError .unrepresentableWire))

private meta def parquet (fail : Bool) : Reader.OpenResult Nat Field Value SourceError :=
  .ok ⟨schema, ⟨[0, 1, 2], fun group =>
    if group = 0 then .ok first
    else if group = 1 then .ok []
    else if fail then .error .lateRead else .ok last, fun _ => .ok ()⟩⟩

#guard (convertParquet db 1 schema codecs (parquet false)).map Result.wire = .ok output
#guard (convertParquet db 1 schema codecs (parquet false)).map (fun result => observed result.db 1) =
  .ok (some cells)
#guard (Reader.denote (parquet true)).map (fun observation => observation.table.rowCount) = .ok 2
#guard (convertParquet db 1 schema codecs (parquet true)).map Result.wire =
  .error (.input (.readError .lateRead))
#guard (convertParquet db 1 schema codecs (.error SourceError.openFailure :
    Reader.OpenResult Nat Field Value SourceError)).map Result.wire = .error (.input (.openError .openFailure))

private meta def zero : Typed.Schema Bool := ⟨0, fun i => i.elim0⟩

private meta def emptyRows (count : Nat) : Typed.Table zero Value :=
  List.replicate count (fun i => i.elim0)

private meta def zeroStream : Events.EventStream Field Value SourceError :=
  .ok ⟨zero, ⟨[AlignedColumns.ofRows (emptyRows 2), AlignedColumns.ofRows (emptyRows 1)], .eos⟩⟩

#guard (convert db 1 zero codecs zeroStream).map (fun result => (observed result.db 1, result.wire)) =
  .ok (some [[], [], []], bytes "\"\"\r\n\"\"\r\n\"\"\r\n\"\"\r\n")

end Silmaril.Formats.Csv.EventStream
