module

import Silmaril.Formats.Arrow.TimestampStream.Writer.Thms
meta import Silmaril.Formats.Arrow.TimestampStream.Writer.Defs

open Silmaril.Formats
open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.TimestampStream.Writer
open Silmaril.Numeric.Timestamp (TickUnit)

private def bind (unit : TickUnit) (zone : Option String) (nullable : Bool := true) :
    TimestampBatch.Binding :=
  ⟨"時刻-é", nullable, ⟨unit, zone⟩⟩

private def batches (binding : TimestampBatch.Binding) : List (TimestampBatch.Column binding) :=
  [[some ⟨-9223372036854775808⟩, none, some ⟨-1⟩, some ⟨0⟩, some ⟨9223372036854775807⟩],
   [], [none, some ⟨87654321⟩]]

private def expected : List (List (Option Int)) :=
  [[some (-9223372036854775808), none, some (-1), some 0, some 9223372036854775807],
   [], [none, some 87654321]]

private def observe (limits : ObservationLimits) (binding : TimestampBatch.Binding)
    (input : List (TimestampBatch.Column binding)) :
    Except TimestampStream.Writer.Error
      ((String × Bool × TickUnit × Option String) × List (List (Option Int))) := do
  let wire ← emit limits binding input
  let read ← (TimestampStream.read limits.ipc wire).mapError .readback
  return (descriptor read.binding, read.batches.map TimestampBatch.Writer.tickCounts)

#guard ([.second, .millisecond, .microsecond, .nanosecond] : List TickUnit).all fun unit =>
  [none, some "UTC"].all fun zone =>
    let binding := bind unit zone
    decide (observe {} binding (batches binding) = .ok (("時刻-é", true, unit, zone), expected))

private def localField := bind .microsecond none
private def utcField := bind .microsecond (some "UTC")
private def required := bind .nanosecond (some "UTC") false

#guard observe {} required [[some ⟨-1⟩], [], [some ⟨2⟩]] =
  .ok (("時刻-é", false, .nanosecond, some "UTC"), [[some (-1)], [], [some 2]])
#guard observe {} localField [] = .ok (("時刻-é", true, .microsecond, none), [])
#guard observe {} utcField [[]] = .ok (("時刻-é", true, .microsecond, some "UTC"), [[]])

#guard (emitSchema {} (bind .second (some ""))) matches .error (.timezone (some ""))
#guard (emit {} (bind .nanosecond (some "Asia/Kathmandu")) []) matches
  .error (.timezone (some "Asia/Kathmandu"))
#guard (emitSchema { fields := 0 } utcField) matches .error (.writer (.limit .fields))
#guard (emitSchema { metadataBytes := Internal.schemaSize localField } localField).isOk
#guard (emitSchema { metadataBytes := Internal.schemaSize localField } utcField) matches
  .error (.writer (.limit .metadataBytes))

#guard observe { ipc.batches := 2 } localField (batches localField) = .error (.writer (.limit .batches))
#guard observe { totalRows := 6 } localField (batches localField) = .error (.writer (.limit .totalRows))
#guard observe { totalCells := 6 } localField (batches localField) = .error (.writer (.limit .totalCells))
#guard observe { ipc.rows := 0 } localField (batches localField) = .error (.record 0 (.writer (.limit .rows)))
#guard observe { ipc.bodyBytes := 0 } localField (batches localField) =
  .error (.record 0 (.writer (.limit .bodyBytes)))
#guard observe {} required [[], [none]] = .error (.record 1 .requiredNull)
#guard observe {} localField [[], [some ⟨9223372036854775808⟩]] =
  .error (.record 1 (.payload .outOfRange))
#guard observe {} utcField [[], [some ⟨-9223372036854775809⟩]] =
  .error (.record 1 (.payload .outOfRange))
