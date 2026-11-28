module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Int96.Dictionary.File.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Int96.Dictionary.File.Defs
meta import Silmaril.Numeric.Timestamp.Defs

open Silmaril.Formats
open Silmaril.Formats.Parquet.Int96 Silmaril.Formats.Parquet.Int96.Dictionary.File
open Silmaril.Numeric.Timestamp

private def v1 : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-dictionary-file/required-v1.parquet"⟩
private def v2 : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-dictionary-file/optional-v2.parquet"⟩
private def badReference : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-dictionary-file/v2-reference.parquet"⟩
private def badWord : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-dictionary-file/v2-word.parquet"⟩
private def unselected : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-dictionary-file/v2-unselected.parquet"⟩
private def overlap : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-dictionary-file/v2-overlap.parquet"⟩
private def footerReordered : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-dictionary-file/v2-reordered.parquet"⟩
private def plain : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-file/optional-v2.parquet"⟩

private def nanos {policy : Policy} (slots : Dictionary.Slots policy) : List (Option Int) :=
  slots.map (Option.map Ticks.ticks)

private def observe (limits : Limits) (source : Bytes) (layout : Parquet.FlatColumn.Layout)
    (policy : Policy) : Except OpenError (List (List (Option Int)) × Option ReadError) :=
  (readFile limits source "legacy_ts" layout policy).map fun trace =>
    (trace.groups.map nanos, trace.failure)

private def v1Groups : List (List (Option Int)) :=
  [[some (-9223372036854775808), some (-1), some 9223372036854775807, some (-1),
    some (-9223372036854775808), some 9223372036854775807],
   [some 6, some (-7), some 8, some 6, some (-7), some 8],
   [some 11, some 12, some 13, some 11, some 12, some 13]]

private def first : List (Option Int) :=
  [some (-2000), none, some (-1000), some (-2000), some 10000000000000000000, some (-1000)]
private def second : List (Option Int) :=
  [some 6000, some (-7000), none, some 6000, some 8000, none]
private def third : List (Option Int) :=
  [none, some 0, some 21000, some 22000, none, some 21000]

private def referenceError : ReadError :=
  .chunk 1 1 "legacy_ts" ⟨180, .page 1 230 (.reference 3 3)⟩
private def wordError : ReadError :=
  .chunk 1 1 "legacy_ts" ⟨180, .page 0 180 (.dictionaryEntry (.invalidWord 1))⟩

#guard observe {} v1 .required .prolepticUtc = .ok (v1Groups, none)
#guard observe {} v1 .required .prolepticLocal = .ok (v1Groups, none)
#guard observe {} v2 .optional .prolepticUtc = .ok ([first, second, third], none)
#guard observe {} v2 .optional .prolepticLocal = .ok ([first, second, third], none)
#guard observe {} badReference .optional .prolepticUtc = .ok ([first], some referenceError)
#guard observe {} badReference .optional .prolepticLocal = .ok ([first], some referenceError)
#guard observe {} badWord .optional .prolepticUtc = .ok ([first], some wordError)
#guard observe {} badWord .optional .prolepticLocal = .ok ([first], some wordError)
#guard observe {} unselected .optional .prolepticLocal = .ok ([first, second, third], none)
#guard observe {} overlap .optional .prolepticLocal = .error (.preflight (.overlap 0 1))
#guard observe {} footerReordered .optional .prolepticLocal = .ok ([second, first, third], none)

private def lookupGroup (source : Bytes) (index : Nat) :
    Except OpenError (Except ReadError (List (Option Int))) :=
  (openFile {} source "legacy_ts" .optional .prolepticLocal).map fun checked =>
    (checked.readGroup index).map nanos

#guard lookupGroup badReference 1 = .ok (.error referenceError)
#guard lookupGroup badWord 1 = .ok (.error wordError)
#guard lookupGroup badReference 2 = .ok (.ok third)
#guard lookupGroup v2 3 = .ok (.error (.selection (.groupIndex 3)))

private def selection (name : String) (layout : Parquet.FlatColumn.Layout) :
    Except OpenError (Nat × Nat × Nat) := do
  let checked ← openFile {} v2 name layout .prolepticLocal
  return (checked.bound.binding.leafOrdinal, checked.bound.binding.columnOrdinal,
    checked.bound.snapshot.groupCount)

#guard selection "legacy_ts" .optional = .ok (2, 1, 3)
#guard selection "decoy" .required = .error (.binding
  (.binding (.leafMismatch 0 ⟨"decoy", .int96, .required⟩)))
#guard selection "legacy_ts" .required = .error (.binding
  (.binding (.leafMismatch 1 ⟨"legacy_ts", .int96, .required⟩)))

private def defaults : Limits := {}

#guard observe { defaults with maxTotalRows := 17 } v2 .optional .prolepticLocal =
  .error (.binding (.rowLimit 17 18))
#guard observe { defaults with maxTotalRows := 18 } v2 .optional .prolepticLocal =
  .ok ([first, second, third], none)
#guard observe { defaults with chunk.maxEntries := 2 } v2 .optional .prolepticLocal =
  .ok ([], some (.chunk 0 1 "legacy_ts" ⟨52, .page 0 52 .entryLimit⟩))
#guard (match observe {} plain .optional .prolepticLocal with
  | .ok ([], some (.chunk 0 1 "legacy_ts" ⟨_, .encodingMetadata⟩)) => true
  | _ => false)
