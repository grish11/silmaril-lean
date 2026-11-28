module

import Silmaril.Formats.Parquet.Timestamp.FromIpc.Thms
import Silmaril.Formats.Arrow.TimestampStream.Writer.Defs
meta import Silmaril.Formats.Parquet.Timestamp.FromIpc.Defs
meta import Silmaril.Formats.Arrow.TimestampStream.Writer.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp.FromIpc

private def localField : Arrow.TimestampBatch.Binding := ⟨"time", true, ⟨.microsecond, none⟩⟩
private def utcField : Arrow.TimestampBatch.Binding := ⟨"time", false, ⟨.nanosecond, some "UTC"⟩⟩

private def input (field : Arrow.TimestampBatch.Binding) (batches : List (Arrow.TimestampBatch.Column field)) :
    KBytes :=
  (Arrow.TimestampStream.Writer.emit {} field batches).toOption.getD KBytes.empty

private def source : KBytes := input localField [[some ⟨-1⟩, none], [], [], [some ⟨2⟩]]

private def observe (wire : KBytes) :
    Option (String × Bool × Parquet.Timestamp.Descriptor × List (List (Option Int))) := do
  let file ← (convert {} {} wire).toOption
  let bound ← (Parquet.Timestamp.Leaf.openLeaf {} file 1).toOption
  let groups ← (Internal.readGroups {} bound).toOption
  return (bound.binding.leaf.name, bound.binding.leaf.repetition == some .optional,
    bound.binding.descriptor, groups.map Internal.counts)

private def exact (wire : KBytes) (nullable adjusted : Bool) (unit : ColumnarTimestamp.Parquet.TimeUnit)
    (groups : List (List (Option Int))) : Bool :=
  match observe wire with
  | some (name, optional, descriptor, actual) =>
    name == "time" && optional == nullable && descriptor.unit == unit &&
      descriptor.isAdjustedToUTC == adjusted && actual == groups
  | none => false

#guard exact source true false .micros [[some (-1), none], [], [], [some 2]]
#guard exact (input utcField [[some ⟨-9223372036854775808⟩], [], [],
    [some ⟨9223372036854775807⟩]]) false true .nanos
  [[some (-9223372036854775808)], [], [], [some 9223372036854775807]]
#guard exact (input utcField []) false true .nanos []

private def failure (limits : Limits) (wire : KBytes) : Option Error :=
  match convert {} limits wire with
  | .error cause => some cause
  | .ok _ => none

#guard failure { maxInputBytes := 0 } source == some .inputByteLimit
#guard failure { maxGroups := 3 } source == some .groupLimit
#guard failure { maxTotalRows := 2 } source == some .totalRows
#guard failure { maxFileBytes := 4 } source == some .fileLimit
#guard failure { leaf.framing.maxPages := 0 } source == some (.pageLimit 0)
#guard failure { leaf.maxRows := 1 } source == some (.pageLimit 0)
#guard failure { snapshot.footer.maxFooterBytes := 0 } source == some (.footer .byteLimit)
#guard (descriptor ⟨"time", true, ⟨.second, some "UTC"⟩⟩) matches .error .seconds
#guard (descriptor ⟨"time", true, ⟨.nanosecond, some ""⟩⟩) matches .error (.timezone "")
