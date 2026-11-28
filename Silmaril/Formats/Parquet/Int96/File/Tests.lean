module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Int96.File.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Int96.File.Defs
meta import Silmaril.Numeric.Timestamp.Defs

/-! Independent multi-column, multi-page files and a corrupt later group. -/

open Silmaril.Formats
open Silmaril.Formats.Parquet.Int96 Silmaril.Formats.Parquet.Int96.File
open Silmaril.Numeric.Timestamp

private def requiredV1 : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-int96-file/required-v1.parquet"⟩
private def optionalV2 : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-int96-file/optional-v2.parquet"⟩
private def damagedV2 : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-int96-file/optional-v2-bad-word.parquet"⟩

private def signedCounts {interpretation : Policy} (slots : Slots interpretation) :
    List (Option Int) :=
  slots.map (Option.map Ticks.ticks)

private def observe (limits : Limits) (source : Bytes) (layout : Parquet.FlatColumn.Layout)
    (interpretation : Policy) : Except OpenError (List (List (Option Int)) × Option ReadError) :=
  (readFile limits source "legacy_ts" layout interpretation).map fun trace =>
    (trace.groups.map signedCounts, trace.failure)

private def requiredGroups : List (List (Option Int)) :=
  [[some (-9223372036854775808), some (-86400000000001), some (-86400000000000), some (-1), some 0,
    some 9223372036854775807],
   [some 11, some (-12), some 13, some (-14), some 15, some (-16)],
   [some 21, some 22, some 23, some 24, some 25, some 26]]

private def first : List (Option Int) :=
  [some (-14826671999999999000), none, some (-1001000), some 0, none, some 13000]
private def second : List (Option Int) :=
  [none, some (-4000), some 5000, none, some 1000, some 10000000000000000000]
private def third : List (Option Int) :=
  [some 21000, none, some 23000, some 24000, some 25000, none]

private def badWord : ReadError :=
  .page 1 1 "legacy_ts" 1 298 (.decode (.invalidWord 2))

#guard observe {} requiredV1 .required .prolepticUtc = .ok (requiredGroups, none)
#guard observe {} optionalV2 .optional .prolepticUtc = .ok ([first, second, third], none)
#guard observe {} optionalV2 .optional .prolepticLocal = .ok ([first, second, third], none)
#guard observe {} damagedV2 .optional .prolepticUtc = .ok ([first], some badWord)
#guard observe {} damagedV2 .optional .prolepticLocal = .ok ([first], some badWord)

private def observedSelection : Except OpenError (Nat × Nat × Nat) := do
  let checked ← openFile {} optionalV2 "legacy_ts" .optional .prolepticLocal
  return (checked.binding.leafOrdinal, checked.binding.columnOrdinal, checked.snapshot.groupCount)

#guard observedSelection = .ok (2, 1, 3)

private def group (source : Bytes) (index : Nat) :
    Except OpenError (Except ReadError (List (Option Int))) :=
  (openFile {} source "legacy_ts" .optional .prolepticLocal).map fun checked =>
    (checked.readGroup index).map signedCounts

#guard group damagedV2 1 = .ok (.error badWord)
#guard group damagedV2 2 = .ok (.ok third)
#guard group optionalV2 3 = .ok (.error (.groupIndex 3))

private def select (name : String) (layout : Parquet.FlatColumn.Layout) :=
  (openFile {} optionalV2 name layout .prolepticLocal).map (fun _ => ())

#guard select "decoy" .required = .error (.binding (.leafMismatch 0 ⟨"decoy", .int96, .required⟩))
#guard select "legacy_ts" .required =
  .error (.binding (.leafMismatch 1 ⟨"legacy_ts", .int96, .required⟩))
#guard select "missing" .optional = .error (.binding (.unknownLeaf "missing"))

private def defaults : Limits := {}

#guard observe { defaults with maxFileBytes := 941 } optionalV2 .optional .prolepticLocal =
  .error (.fileByteLimit 941 942)
#guard observe { defaults with maxTotalRows := 17 } optionalV2 .optional .prolepticLocal =
  .error (.rowLimit 17 18)
#guard observe { defaults with maxTotalRows := 18 } optionalV2 .optional .prolepticLocal =
  .ok ([first, second, third], none)
#guard observe { defaults with column.maxRows := 5 } optionalV2 .optional .prolepticLocal =
  .ok ([], some (.column 0 1 "legacy_ts" (.rowLimit 5 6)))
#guard observe { defaults with column.framing.maxPages := 1 } optionalV2 .optional .prolepticLocal =
  .ok ([], some (.column 0 1 "legacy_ts" (.framing .pageLimit)))
