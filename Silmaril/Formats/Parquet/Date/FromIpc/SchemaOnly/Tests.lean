module

meta import Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly.Defs
meta import Silmaril.Formats.Parquet.Date.Events.ToIpc.Defs
meta import Silmaril.Formats.Parquet.Date.FromIpc.Multi.Defs

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly

private meta def limits : Limits := ⟨4096, {}⟩

private meta def observes (name : String) (nullable : Bool) : Bool :=
  ((do
    let source ← (Arrow.DateStream.Writer.emit {} name nullable []).toOption
    let file ← (convert {} limits {} source).toOption
    let checked ← (Date.openChecked {} file).toOption
    let stream ← (Date.Events.ToIpc.convert {} {} file).toOption
    let read ← (Arrow.DateStream.read {} stream).toOption
    return decide (Matches checked ⟨name, nullable, .day⟩) &&
      checked.snapshot.metadata.rowGroups.isEmpty &&
      read == Arrow.DateStream.Writer.observation name nullable [] &&
      (match Date.readGroup {} file 0 with | .error (.groupIndex 0) => true | _ => false)
    : Option Bool)).getD false

#guard observes "日付" true
#guard observes "époque" false

private meta def rejects (writer : Limits) (batches : List Arrow.DateStream.Writer.Column)
    (expected : Date.FromIpc.Error) : Bool :=
  match Arrow.DateStream.Writer.emit {} "date" false batches with
  | .error _ => false
  | .ok source =>
    match convert {} writer {} source with
    | .ok _ => false
    | .error actual => actual == expected

#guard rejects limits [[]] (.batchCount 1)
#guard rejects limits [[some (-1)]] (.batchCount 1)
#guard rejects { limits with maxFileBytes := 11 } [] (.writer .fileLimit)
#guard rejects { limits with footer.maxFooterBytes := 0 } [] (.writer (.compact .byteLimit))
#guard rejects { limits with footer.compact.maxCollectionSize := 1 } [] (.writer .schemaOrCount)
#guard rejects { limits with footer.compact.maxBinaryBytes := 4 } [] (.writer .schemaOrCount)

#guard match Arrow.DateStream.Writer.emit {} "date" false [] with
  | .error _ => false
  | .ok source =>
    let writer : Date.FromIpc.Multi.Limits := ⟨⟨1, 4096, {}, ⟨{}, 64, ⟨64, 256, ⟨16, 64⟩, 0⟩⟩⟩, 4, 8⟩
    match Date.FromIpc.Multi.convert {} writer {} source with
    | .error (.source (.batchCount 0)) => true
    | _ => false

#guard match Arrow.DateStream.Writer.emit {} "date" false [] with
  | .error _ => false
  | .ok source =>
    match convert {} { limits with maxFileBytes := 0 } {} (source.slice 0 (source.len - 8)) with
    | .error (.reader (.batch 0 (.envelope (.malformed .truncated)))) => true
    | _ => false
