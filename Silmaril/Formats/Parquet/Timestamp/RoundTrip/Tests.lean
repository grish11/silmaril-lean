module

import Silmaril.Formats.Parquet.Timestamp.RoundTrip.Thms
meta import Silmaril.Formats.Parquet.Timestamp.RoundTrip.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp

private def field : Arrow.TimestampBatch.Binding := ⟨"時刻", true, ⟨.microsecond, none⟩⟩

private def sourceBatches : List (Arrow.TimestampBatch.Column field) :=
  [[some ⟨-9223372036854775808⟩, none], [], [], [some ⟨9223372036854775807⟩]]

private def fixture (batches : List (Arrow.TimestampBatch.Column field)) : KBytes :=
  (Arrow.TimestampStream.Writer.emit {} field batches).toOption.getD KBytes.empty

private def source : KBytes := fixture sourceBatches

private def verify (batches : List (Arrow.TimestampBatch.Column field)) : Bool := Id.run do
  let wire := fixture batches
  let inputLimits : Arrow.Limits := {batches := 4, rows := 2}
  let reverse : FromIpc.Limits :=
    {maxInputBytes := 4096, maxFileBytes := 4096, maxGroups := 6, maxTotalRows := 8}
  let forward : Leaf.Events.ToIpc.Limits :=
    {maxFileBytes := 2048, maxGroups := 4, maxTotalRows := 3}
  let sink : Arrow.ObservationLimits :=
    {ipc := {batches := 4, rows := 2, bodyBytes := 24, metadataBytes := 256},
      totalRows := 3, totalCells := 3}
  let .ok middle := FromIpc.convert inputLimits reverse wire | return false
  let .ok output := Leaf.Events.ToIpc.convert forward sink middle 1 | return false
  let .ok read := Arrow.TimestampStream.read sink.ipc output | return false
  return Arrow.TimestampStream.Writer.descriptor read.binding ==
      Arrow.TimestampStream.Writer.descriptor field &&
    read.batches.map Arrow.TimestampBatch.Writer.tickCounts ==
      batches.map Arrow.TimestampBatch.Writer.tickCounts

#guard verify sourceBatches
#guard verify [[], [], []]
#guard verify []

#guard FromIpc.convert {} {maxInputBytes := 0} source matches .error .inputByteLimit
#guard FromIpc.convert {batches := 3} {} source matches .error (.source (.batch 3 .batchLimit))

private def failure (forward : Leaf.Events.ToIpc.Limits) (sink : Arrow.ObservationLimits) : Option Leaf.Events.ToIpc.Error := do
  let middle ← (FromIpc.convert {} {} source).toOption
  match Leaf.Events.ToIpc.convert forward sink middle 1 with
  | .error cause => some cause
  | .ok _ => none

-- The Parquet snapshot and leaf settings match certification in each case.
#guard failure {maxFileBytes := 0} {} matches some (.fileByteLimit 0 _)
#guard failure {maxGroups := 3} {} == some (.groupLimit 3 4)
#guard failure {maxTotalRows := 2} {} == some (.rowLimit 2 3)
#guard failure {} {ipc.batches := 3} == some (.writer (.writer (.limit .batches)))
#guard failure {} {totalRows := 2} == some (.writer (.writer (.limit .totalRows)))
#guard failure {} {totalCells := 2} == some (.writer (.writer (.limit .totalCells)))
#guard failure {} {ipc.metadataBytes := 0} == some (.writer (.writer (.limit .metadataBytes)))
#guard failure {} {ipc.rows := 1} == some (.writer (.record 0 (.writer (.limit .rows))))
#guard failure {} {ipc.bodyBytes := 0} == some (.writer (.record 0 (.writer (.limit .bodyBytes))))
