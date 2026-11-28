module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Int96.Mixed.File.Events.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Int96.Mixed.File.Events.Defs
meta import Silmaril.Numeric.Timestamp.Defs

open Silmaril.Formats
open Silmaril.Formats.Parquet.Int96
open Silmaril.Formats.Parquet.Int96.Mixed.File.Events
open Silmaril.Numeric.Timestamp (TickUnit Ticks)

private def v1 : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-int96-mixed-file/fallback-v1.parquet"⟩
private def v2 : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-int96-mixed-file/fallback-v2.parquet"⟩
private def v2Empty : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-int96-arrow-events/v2-empty.parquet"⟩
private def v2Precision : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-int96-arrow-events/v2-precision.parquet"⟩
private def v2BadReference : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-int96-mixed-file/v2-reference.parquet"⟩
private def v1BadWord : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-int96-mixed-file/v1-word.parquet"⟩
private def endpoints : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-int96-dictionary-file/required-v1.parquet"⟩

private structure Observation where
  name : String
  unit : TickUnit
  timezone : Option String
  nullable : Bool
  values : List (List (Option Int))
  ending : Arrow.Events.Termination Error
  deriving DecidableEq

private def observe (source : Bytes) (policy : Policy) (unit : TickUnit)
    (layout : Parquet.FlatColumn.Layout := .optional) (limits : Mixed.File.Limits := {}) :
    Except Error (Option Observation) :=
  (readAll limits "legacy_ts" layout policy unit source).map fun ⟨schema, trace⟩ =>
    if h : 0 < schema.width then
      let field : Fin schema.width := ⟨0, h⟩
      let (name, kind) := schema.kind field
      let values := trace.batches.map fun batch => (batch.values field).map (Option.map Ticks.ticks)
      some ⟨name, kind.metadata.unit, kind.metadata.timezone, kind.nullable, values, trace.termination⟩
    else none

private def group (last shift : Int) : List (Option Int) :=
  ([some (-1), none, some 17, some (-1), some 3, none, some 17, some last,
    some 101, none, some (-102), some 103, some 104, none, some (-105), some 106,
    some 107, none, some 108, some 109, some 110, some 111, none, some 113] : List (Option Int)).map
      (Option.map (· + shift))

private def v1Groups : List (List (Option Int)) := [group 19 0, group 19 1000, group 19 (-2000)]
private def v2Groups : List (List (Option Int)) :=
  [group (-1) 0, [], group (-1) 10000000000000000, group (-1) (-10000000000000000)]

#guard observe v1 .prolepticUtc .nanosecond =
  .ok (some ⟨"legacy_ts", .nanosecond, some "UTC", true, v1Groups, .eos⟩)
#guard observe v1 .prolepticLocal .nanosecond =
  .ok (some ⟨"legacy_ts", .nanosecond, none, true, v1Groups, .eos⟩)
#guard observe v2Empty .prolepticUtc .microsecond =
  .ok (some ⟨"legacy_ts", .microsecond, some "UTC", true, v2Groups, .eos⟩)
#guard observe v2Empty .prolepticLocal .microsecond =
  .ok (some ⟨"legacy_ts", .microsecond, none, true, v2Groups, .eos⟩)

private def firstV2Nanos : List (Option Int) := (group (-1) 0).map (Option.map (· * 1000))

#guard observe v2 .prolepticUtc .nanosecond =
  .ok (some ⟨"legacy_ts", .nanosecond, some "UTC", true, [firstV2Nanos],
    .readError (.narrowFailure 1 ⟨0, .outOfRange⟩)⟩)
#guard observe v2Precision .prolepticLocal .microsecond =
  .ok (some ⟨"legacy_ts", .microsecond, none, true, [group (-1) 0],
    .readError (.narrowFailure 1 ⟨10, .precisionLoss⟩)⟩)

-- The corrupt group has an out-of-range first tick on the nanos scale.
-- Its original source error is reached before any narrowing in that group.
#guard observe v2BadReference .prolepticUtc .nanosecond =
  .ok (some ⟨"legacy_ts", .nanosecond, some "UTC", true, [firstV2Nanos],
    .readError (.groupFailure 1 (.chunk 1 1 "legacy_ts" ⟨601, .page 2 680 (.dictionary (.reference 3 3))⟩))⟩)

-- An earlier group narrowing error terminates the trace before a later source failure.
#guard observe v1BadWord .prolepticLocal .microsecond =
  .ok (some ⟨"legacy_ts", .microsecond, none, true, [],
    .readError (.narrowFailure 0 ⟨0, .precisionLoss⟩)⟩)

#guard (observe endpoints .prolepticUtc .nanosecond .required).toOption.map
    (Option.map fun result => (result.nullable, result.values.head?.map (·.take 3))) =
   some (some (false, some [some (-9223372036854775808), some (-1), some 9223372036854775807]))

#guard narrowSlots .prolepticLocal .second [some ⟨-1000000000⟩, none, some ⟨0⟩] =
  .ok [some ⟨-1⟩, none, some ⟨0⟩]
#guard narrowSlots .prolepticUtc .millisecond [some ⟨-1000000⟩, none, some ⟨1000000⟩] =
  .ok [some ⟨-1⟩, none, some ⟨1⟩]
#guard narrowSlots .prolepticLocal .microsecond [some ⟨0⟩, none, some ⟨-1⟩] =
  .error ⟨2, .precisionLoss⟩

#guard observe v2Empty .prolepticUtc .microsecond .optional { maxTotalRows := 71 } =
  .error (.openFailure (.binding (.rowLimit 71 72)))
