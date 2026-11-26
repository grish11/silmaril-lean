module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Int96.Mixed.File.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Int96.Mixed.File.Defs
meta import Silmaril.Numeric.Timestamp.Defs

open Silmaril.Formats
open Silmaril.Formats.Parquet.Int96 Silmaril.Formats.Parquet.Int96.Mixed.File
open Silmaril.Numeric.Timestamp

private def v1 : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-mixed-file/fallback-v1.parquet"⟩
private def v2 : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-mixed-file/fallback-v2.parquet"⟩
private def badWord : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-mixed-file/v1-word.parquet"⟩
private def badReference : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-mixed-file/v2-reference.parquet"⟩
private def unselected : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-mixed-file/v2-unselected.parquet"⟩
private def overlap : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-mixed-file/v2-overlap.parquet"⟩
private def reordered : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-mixed-file/v2-reordered.parquet"⟩
private def plainOnly : Bytes :=
  ⟨include_bytes "../../../../../../data/parquet-int96-file/optional-v2.parquet"⟩

private def nanos {policy : Policy} (slots : Dictionary.Slots policy) : List (Option Int) :=
  slots.map (Option.map Ticks.ticks)

private def baseGroup (lastReference : Int) : List (Option Int) :=
  [some (-1), none, some 17, some (-1), some 3, none, some 17, some lastReference,
   some 101, none, some (-102), some 103, some 104, none, some (-105), some 106,
   some 107, none, some 108, some 109, some 110, some 111, none, some 113]

private def expectedGroup (scale shift lastReference : Int) : List (Option Int) :=
  (baseGroup lastReference).map (Option.map fun count => (count + shift) * scale)

private def firstV1 : List (Option Int) := expectedGroup 1 0 19
private def secondV1 : List (Option Int) := expectedGroup 1 1000 19
private def thirdV1 : List (Option Int) := expectedGroup 1 (-2000) 19
private def firstV2 : List (Option Int) := expectedGroup 1000 0 (-1)
private def secondV2 : List (Option Int) := expectedGroup 1000 10000000000000000 (-1)
private def thirdV2 : List (Option Int) := expectedGroup 1000 (-10000000000000000) (-1)

private def observe (limits : Limits) (source : Bytes) (policy : Policy) :
    Except OpenError (List (List (Option Int)) × Option ReadError) :=
  (readFile limits source "legacy_ts" .optional policy).map fun trace => (trace.groups.map nanos, trace.failure)

private def wordError : ReadError :=
  .chunk 1 1 "legacy_ts" ⟨589, .page 3 708 (.plain (.invalidWord 2))⟩
private def referenceError : ReadError :=
  .chunk 1 1 "legacy_ts" ⟨601, .page 2 680 (.dictionary (.reference 3 3))⟩

#guard observe {} v1 .prolepticUtc = .ok ([firstV1, secondV1, thirdV1], none)
#guard observe {} v1 .prolepticLocal = .ok ([firstV1, secondV1, thirdV1], none)
#guard observe {} v2 .prolepticUtc = .ok ([firstV2, secondV2, thirdV2], none)
#guard observe {} v2 .prolepticLocal = .ok ([firstV2, secondV2, thirdV2], none)
#guard observe {} badWord .prolepticUtc = .ok ([firstV1], some wordError)
#guard observe {} badWord .prolepticLocal = .ok ([firstV1], some wordError)
#guard observe {} badReference .prolepticUtc = .ok ([firstV2], some referenceError)
#guard observe {} badReference .prolepticLocal = .ok ([firstV2], some referenceError)
#guard observe {} unselected .prolepticLocal = .ok ([firstV2, secondV2, thirdV2], none)
#guard observe {} overlap .prolepticLocal = .error (.preflight (.overlap 0 1))
#guard observe {} reordered .prolepticLocal = .ok ([secondV2, firstV2, thirdV2], none)

private def lookup (source : Bytes) (index : Nat) :
    Except OpenError (Except ReadError (List (Option Int))) :=
  (openFile {} source "legacy_ts" .optional .prolepticLocal).map fun checked =>
    (checked.readGroup index).map nanos

#guard lookup badWord 2 = .ok (.ok thirdV1)
#guard lookup badReference 2 = .ok (.ok thirdV2)
#guard lookup badReference 1 = .ok (.error referenceError)
#guard lookup v2 3 = .ok (.error (.selection (.groupIndex 3)))

private def selection (name : String) (layout : Parquet.FlatColumn.Layout) :
    Except OpenError (Nat × Nat × Nat) := do
  let checked ← openFile {} v2 name layout .prolepticUtc
  return (checked.selection.bound.binding.leafOrdinal, checked.selection.bound.binding.columnOrdinal,
    checked.selection.bound.snapshot.groupCount)

#guard selection "legacy_ts" .optional = .ok (2, 1, 3)
#guard selection "decoy" .required =
  .error (.binding (.binding (.leafMismatch 0 ⟨"decoy", .int96, .required⟩)))
#guard selection "legacy_ts" .required =
  .error (.binding (.binding (.leafMismatch 1 ⟨"legacy_ts", .int96, .required⟩)))

private def limits : Limits := {}

#guard observe { limits with maxTotalRows := 71 } v2 .prolepticLocal =
  .error (.binding (.rowLimit 71 72))
#guard observe { limits with maxTotalRows := 72 } v2 .prolepticLocal =
  .ok ([firstV2, secondV2, thirdV2], none)
#guard observe { limits with maxFileBytes := v2.length - 1 } v2 .prolepticLocal =
  .error (.binding (.fileByteLimit (v2.length - 1) v2.length))
#guard observe { limits with chunk.maxChunkBytes := 308 } v2 .prolepticLocal =
  .ok ([], some (.chunk 0 1 "legacy_ts" ⟨148, .locate .chunkLimit⟩))
#guard observe { limits with chunk.maxEntries := 3 } v1 .prolepticLocal =
  .ok ([], some (.chunk 0 1 "legacy_ts" ⟨138, .page 0 138 (.dictionary .entryLimit)⟩))
#guard observe { limits with chunk.framing.maxPages := 4 } v2 .prolepticLocal =
  .ok ([], some (.chunk 0 1 "legacy_ts" ⟨148, .framing .pageLimit⟩))

#guard (match observe {} plainOnly .prolepticLocal with
  | .ok ([], some (.chunk 0 1 "legacy_ts" ⟨_, .locate .encodingMetadata⟩)) => true
  | _ => false)

private def dictionaryOnly : Except Dictionary.File.OpenError (Option Dictionary.File.ReadError) :=
  (Dictionary.File.readFile {} v2 "legacy_ts" .optional .prolepticLocal).map (·.failure)

#guard dictionaryOnly = .ok (some (.chunk 0 1 "legacy_ts" ⟨148, .page 3 257 (.dataEncoding 0)⟩))
