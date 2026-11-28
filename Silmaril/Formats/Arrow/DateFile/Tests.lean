module

meta import Silmaril.Formats.Arrow.DateFile.Defs
meta import Silmaril.Formats.Arrow.DateFile.Fixture

open Silmaril Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.DateFile

private meta def days (column : DateValues.Column) : List (Option Int) :=
  column.map fun cell => cell.bind (·.toEpochDay?)

private meta def sameField (field : DateStream.Field) (unit : SchemaReader.DateUnit)
    (nullable : Bool) : Bool :=
  field.name == "日付" && field.unit == unit && field.nullable == nullable

private meta def indexes (input : KBytes) (unit : SchemaReader.DateUnit) (nullable : Bool)
    (expected : List (List (Option Int))) : Bool := Id.run do
  let .ok index := DateFile.readIndex {} input | return false
  if !sameField index.field unit nullable || index.blocks.length != expected.length then return false
  let .ok stream := DateStream.read {} (input.slice 8 (index.span.start - 8)) | return false
  if stream.field != index.field || stream.batches.map days != expected then return false
  for n in (List.range expected.length).reverse do
    let .ok (some dates) := index.readAt {} n | return false
    let some block := index.blocks[n]? | return false
    if some dates != stream.batches[n]? then return false
    let metadata := metadataSlice input block
    let body := bodySlice input block
    if DateBatch.decode {} index.schemaMetadata metadata body != .ok dates then return false
    if metadata.toList != (input.toList.drop (block.offset + 8)).take (block.metadataLength - 8) ||
        body.toList != (input.toList.drop (block.offset + block.metadataLength)).take block.bodyLength then
      return false
  match index.readAt {} expected.length with
  | .ok none => return true
  | _ => return false

private meta def failsThirdWithNeighbors (input : KBytes) (cause : BlockError)
    (first : List (Option Int)) : Bool := Id.run do
  let .ok index := DateFile.readIndex {} input | return false
  if index.blocks.length != 3 then return false
  if index.readAt {} 2 != .error (.batch 2 cause) then return false
  let .ok (some empty) := index.readAt {} 1 | return false
  let .ok (some head) := index.readAt {} 0 | return false
  return empty.isEmpty && days head == first

private meta def patch (input : KBytes) (offset width value : Nat) : KBytes :=
  input.slice 0 offset ++ KBytes.leaf width value ++
    input.slice (offset + width) (input.len - (offset + width))

#guard indexes Fixture.date32 .day true
  [[some (-2147483648), some (-1), none], [], [some 11016, some 2147483647]]
#guard indexes Fixture.date64 .millisecond true
  [[some (-106751991167), some (-1), none], [], [some 11016, some 106751991167]]
#guard indexes Fixture.schemaOnly .day false []
#guard failsThirdWithNeighbors Fixture.lateFraction (.values (.nonWholeDay 1)) [some (-1), none]
#guard match DateFile.readIndex {} Fixture.lateFraction with
  | .ok index =>
    match DateStream.read {} (Fixture.lateFraction.slice 8 (index.span.start - 8)) with
    | .error (.batch 2 (.values (.nonWholeDay 1))) => true
    | _ => false
  | .error _ => false
#guard match DateFile.readIndex {} Fixture.wrongFooterUnit with
  | .error .schemaMismatch => true
  | _ => false

#guard failsThirdWithNeighbors
  (patch Fixture.date32 Fixture.metadataLengthOffset 4 Fixture.metadataLengthReplacement)
  .metadataLength [some (-2147483648), some (-1), none]
#guard failsThirdWithNeighbors
  (patch Fixture.date32 Fixture.bodyLengthOffset 8 Fixture.bodyLengthReplacement)
  .bodyLength [some (-2147483648), some (-1), none]
