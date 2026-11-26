module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs
meta import Silmaril.Numeric.Timestamp.Defs

open Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events (Cell Kind)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc
open Silmaril.Numeric.Timestamp (TickUnit)

private def schema (timezone : Option String) : Scan.Schema String Kind :=
  ⟨1, fun _ => ("utc-looking-name", ⟨⟨.microsecond, timezone⟩, true⟩)⟩

private abbrev SourceError := Parquet.Timestamp.Leaf.Events.Error

private def values : List (List (Option Int)) :=
  [[some (-1), none, some 9223372036854775807], [], [some (-9223372036854775808)]]

private def events (timezone : Option String) (termination : Arrow.Events.Termination SourceError := .eos)
    (groups : List (List (Option Int)) := values) : Source :=
  let batches := groups.map fun group =>
    let rows : Parquet.Reader.RowGroup (schema timezone) Cell :=
      group.map fun slot _ => slot.map (fun tick => ⟨tick⟩)
    AlignedColumns.ofRows rows
  .ok ⟨schema timezone, ⟨batches, termination⟩⟩

private def observe (source : Source) :
    Except Error ((String × Bool × TickUnit × Option String) × List (List (Option Int))) := do
  let wire ← emit {} source
  let result ← (Arrow.TimestampStream.read {} wire).mapError (.writer ∘ .readback)
  return (Arrow.TimestampStream.Writer.descriptor result.binding,
    result.batches.map Arrow.TimestampBatch.Writer.tickCounts)

#guard observe (events none) = .ok (("utc-looking-name", true, .microsecond, none), values)
#guard observe (events (some "UTC")) = .ok (("utc-looking-name", true, .microsecond, some "UTC"), values)
#guard observe (events none .eos []) = .ok (("utc-looking-name", true, .microsecond, none), [])
#guard observe (events (some "Asia/Kathmandu")) = .error (.writer (.timezone (some "Asia/Kathmandu")))

private def cause : SourceError := .groupFailure 2 (.page 0 (.scalar (.unsupportedEncoding 8)))

#guard (match emit { ipc.fields := 0 } (events none (.readError cause)) with
  | .error (.source actual) => actual == cause
  | _ => false)
#guard (match emit { ipc.batches := 0 } (events none (.closeError cause)) with
  | .error (.source actual) => actual == cause
  | _ => false)
#guard (emit {} (events none .closed)) matches .error .closed

private def noColumns : Scan.Schema String Kind := ⟨0, Fin.elim0⟩

#guard (emit {} (.ok ⟨noColumns, ⟨[], .eos⟩⟩)) matches .error (.fieldCount 0)

#guard (convert { maxFileBytes := 1 } {} (.ofList [0, 1]) 0) matches .error (.fileByteLimit 1 2)

#guard Parquet.Timestamp.Internal.convertedTimestamp 9 matches .ok ⟨.millis, true⟩
#guard Parquet.Timestamp.Internal.convertedTimestamp 10 matches .ok ⟨.micros, true⟩
#guard Parquet.Timestamp.Internal.convertedTimestamp 11 matches .error (.convertedType 11)
#guard (convertWith .allowConvertedOnly { maxFileBytes := 1 } {} (.ofList [0, 1]) 0)
  matches .error (.fileByteLimit 1 2)

#guard ({} : Parquet.Timestamp.Leaf.Limits).admitsCodec 0
#guard !(({} : Parquet.Timestamp.Leaf.Limits).admitsCodec 1)
#guard ({ allowSnappy := true } : Parquet.Timestamp.Leaf.Limits).admitsCodec 1
#guard !(({ allowSnappy := true } : Parquet.Timestamp.Leaf.Limits).admitsCodec 2)
