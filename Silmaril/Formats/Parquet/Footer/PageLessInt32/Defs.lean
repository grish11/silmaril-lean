module

public import Silmaril.Formats.Parquet.Footer.Defs

/-! Opt-in footer admission for a pinned PyArrow zero-page INT32 convention. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Footer.PageLessInt32

open ThriftCompact
open Traversal (Field Reader)

inductive Error where
  | footer (cause : Footer.Error)
  | validation (cause : ValidationError)
  | traversal (cause : Traversal.Error)
  | profile
  | emptyMetadata (index : Nat)
  | ordinal (index : Nat)
  | layout (index : Nat)
  | dataExtent
  deriving DecidableEq, Repr

/-- No page, value, external offset or auxiliary interval is represented. -/
def isPageLess (group : RowGroup) : Bool :=
  match group.columns with
  | [chunk] =>
    let col := chunk.metadata
    group.numRows == 0 && group.totalByteSize == 0 && group.fileOffset == some 0 &&
      group.totalCompressedSize == some 0 && chunk.fileOffset == 0 &&
      col.physicalType == .int32 && col.encodings == [3] && col.codec == 0 &&
      col.numValues == 0 && col.totalUncompressedSize == 0 && col.totalCompressedSize == 0 &&
      col.dataPageOffset == 0 && col.indexPageOffset.isNone && col.dictionaryPageOffset.isNone &&
      col.bloomFilterOffset.isNone && col.bloomFilterLength.isNone &&
      chunk.offsetIndexOffset.isNone && chunk.offsetIndexLength.isNone &&
      chunk.columnIndexOffset.isNone && chunk.columnIndexLength.isNone
  | _ => false

namespace Internal

abbrev Read (α : Type) := Nat → Except Error (α × Nat)

def structFields (reader : Reader) : Read (List Field) :=
  fun offset => (Traversal.readStruct reader offset).mapError .traversal

def payload {α : Type} (field : Field) (kind : ValueType) (read : Read α) (failure : Error) :
    Except Error α := do
  if field.type ≠ .payload kind then throw failure
  let (value, stop) ← read field.start
  if stop ≠ field.stop then throw failure
  return value

def field (fields : List Field) (id : Int) (failure : Error) : Except Error Field :=
  match fields.filter (·.id == id) with
  | [result] => .ok result
  | _ => .error failure

def groups (reader : Reader) : Except Error (List (List Field)) := do
  let (footer, stop) ← structFields reader 0
  if stop ≠ reader.source.length then throw .profile
  let list ← field footer 4 .profile
  payload list .list (Traversal.readList reader .traversal .struct (structFields reader)) .profile

def checkOrdinal (reader : Reader) (index : Nat) (group : List Field) : Except Error Unit := do
  match group.filter (·.id == 7) with
  | [] => return ()
  | [encoded] =>
    let ordinal ← payload encoded .i16 (fun offset =>
      (readSigned .i16 reader.mode reader.source offset).mapError (.traversal ∘ .compact))
      (.ordinal index)
    if ordinal ≠ (index : Int) then throw (.ordinal index)
  | _ => throw (.ordinal index)

/-- The raw whitelist also excludes fields skipped by the typed projection. -/
def checkEmptyRaw (reader : Reader) (index : Nat) (group : List Field) : Except Error Unit := do
  let failure := Error.emptyMetadata index
  if ((group.filter (·.id != 7)).map (·.id)) ≠ [1, 2, 3, 5, 6] then throw failure
  let colList ← field group 1 failure
  let [chunk] ← payload colList .list (Traversal.readList reader .traversal .struct
    (structFields reader)) failure | throw failure
  if (chunk.map (·.id)) ≠ [2, 3] then throw failure
  let col ← field chunk 3 failure
  let metadata ← payload col .struct (structFields reader) failure
  if (metadata.map (·.id)) ≠ [1, 2, 3, 4, 5, 6, 7, 9, 13] then throw failure
  let stats ← field metadata 13 failure
  let [] ← payload stats .list (Traversal.readList reader .traversal .struct
    (structFields reader)) failure | throw failure

/-- Check in original footer order. Framed chunks cover the entire data
region in strictly increasing, adjacent intervals. Page-less groups take
no interval and do not advance the cursor. -/
def layout (reader : Reader) (name : String) : Nat → Int → List (RowGroup × List Field) →
    Except Error Int
  | _, cursor, [] => .ok cursor
  | index, cursor, (group, raw) :: tail => do
    checkOrdinal reader index raw
    let [column] := group.columns | throw (.layout index)
    let chunkMeta := column.metadata
    if isPageLess group then
      if chunkMeta.pathInSchema ≠ [name] then throw (.emptyMetadata index)
      checkEmptyRaw reader index raw
      layout reader name (index + 1) cursor tail
    else
      let start := chunkMeta.dictionaryPageOffset.getD chunkMeta.dataPageOffset
      if start ≠ cursor || group.fileOffset != some start || column.fileOffset != 0 ||
          group.totalByteSize != chunkMeta.totalUncompressedSize ||
          group.totalCompressedSize != some chunkMeta.totalCompressedSize ||
          column.offsetIndexOffset.isSome || column.columnIndexOffset.isSome ||
          chunkMeta.bloomFilterOffset.isSome || chunkMeta.indexPageOffset.isSome then
        throw (.layout index)
      layout reader name (index + 1) (start + chunkMeta.totalCompressedSize) tail

end Internal

/-- Reuse strict validation for all framed chunks. Only the checked zero-row
metadata convention is omitted from that projection. The original footer
and every ordinal remain in the checked snapshot. -/
def validate (limits : Footer.Limits) (depth : Nat) (source : Bytes) (span : Span)
    (metadata : Metadata) : Except Error Unit :=
  if metadata.version ≠ 2 || metadata.createdBy != some "parquet-cpp-arrow version 26.0.1" then
    .error .profile
  else
    match metadata.schema with
    | [_, leaf] =>
      if leaf.physicalType ≠ some .int32 then .error .profile
      else do
        (Footer.validate span.start depth
          { metadata with rowGroups := metadata.rowGroups.filter (!isPageLess ·) }).mapError .validation
        let reader : Reader := ⟨fileBytes source span.start span.stop, limits.compact, limits.varintMode⟩
        let raw ← Internal.groups reader
        if raw.length ≠ metadata.rowGroups.length then throw .profile
        let stop ← Internal.layout reader leaf.name 0 4 (metadata.rowGroups.zip raw)
        if stop ≠ (span.start : Int) then throw .dataExtent
    | _ => .error .profile

end Silmaril.Formats.Parquet.Footer.PageLessInt32
