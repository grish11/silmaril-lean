module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Compact.Defs
public import Silmaril.Formats.Parquet.PlainV1Writer.Defs
public import Silmaril.Formats.Parquet.Page.Defs
public import Batteries.Data.Except

/-! One flat Parquet row group, with one uncompressed PLAIN INT32 V1 page per column. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatInt32Writer

open Compact (ColumnIndex)

/- The check compares all represented footer fields produced by this profile. -/
deriving instance DecidableEq for Footer.SchemaElement, Footer.ColumnMetadata,
  Footer.ColumnChunk, Footer.RowGroup, Footer.Metadata

structure Column where
  name : String
  values : PlainV1Writer.Input

structure Input where
  rowCount : Nat
  columns : List Column

structure Limits where
  maxColumns : Nat
  maxFileBytes : Nat
  footer : Footer.Limits
  page : PlainV1Writer.Limits

inductive Error where
  | schemaOrCount
  | fileLimit
  | pageBudget
  | page (error : PlainV1Writer.Error)
  | compact (error : Compact.Error)
  | invariant
  deriving DecidableEq, Repr

/-- A nonempty ordered schema with exact, rectangular counts. -/
def Input.Valid (input : Input) (limits : Limits) : Prop :=
  0 < input.columns.length ∧ input.columns.length ≤ limits.maxColumns ∧
    input.columns.length + 1 ≤ limits.footer.compact.maxCollectionSize ∧
    (input.columns.map (·.name)).Nodup ∧
    ∀ column ∈ input.columns, column.values.numValues = input.rowCount ∧
      column.name.utf8ByteSize ≤ limits.footer.compact.maxBinaryBytes

instance (input : Input) (limits : Limits) : Decidable (input.Valid limits) := by
  unfold Input.Valid
  infer_instance

structure Chunk where
  column : Column
  page : PlainV1Writer.Encoded
  start : Nat

def Chunk.stop (chunk : Chunk) : Nat := chunk.start + chunk.page.wire.length

def Chunk.index (chunk : Chunk) : ColumnIndex :=
  ⟨chunk.column.name, (match chunk.column.values with | .required _ => false | .optional _ => true),
    ⟨chunk.start, chunk.stop⟩⟩

def Chunk.frame (chunk : Chunk) : Page.Frame :=
  let split := chunk.start + chunk.page.headerBytes.length
  ⟨chunk.page.header, ⟨chunk.start, split⟩, ⟨split, chunk.stop⟩⟩

def Limits.pageReader (limits : Limits) : Page.Limits := ⟨limits.page.headerBytes, 1, limits.page.header⟩

structure Encoded where
  bytes : Bytes
  footer : Footer.Span
  metadata : Footer.Metadata
  chunks : List Chunk

def measuredPage (limits : PlainV1Writer.Limits) (input : PlainV1Writer.Input) : Except Error Nat := do
  if ¬ input.Fits limits then throw .pageBudget
  let some header := PlainV1Writer.encodeHeader input.numValues input.bodySize | throw .pageBudget
  if limits.headerBytes < header.length then throw .pageBudget
  return header.length + input.bodySize

def emitChunks (limits : PlainV1Writer.Limits) : Nat → List Column → Except Error (List Chunk)
  | _, [] => .ok []
  | start, column :: rest => do
    let page ← (PlainV1Writer.emit limits column.values).mapError Error.page
    let chunk : Chunk := ⟨column, page, start⟩
    let tail ← emitChunks limits chunk.stop rest
    return chunk :: tail

/-- Bounds cover the data and trailer before page assembly. The remaining file
budget also caps the incremental footer encoder. -/
def assembleAnnotated (annotation : Compact.LeafAnnotation) (limits : Limits) (input : Input) :
    Except Error Encoded := do
  let sizes ← input.columns.mapM (fun col => measuredPage limits.page col.values)
  let footerStart := 4 + sizes.sum
  let fileLimit := min limits.maxFileBytes (2 ^ 63 - 1)
  if fileLimit < footerStart + 8 then throw .fileLimit
  let chunks ← emitChunks limits.page 4 input.columns
  let indexes := chunks.map Chunk.index
  let footerLimit := min (min limits.footer.maxFooterBytes (2 ^ 32 - 1)) (fileLimit - footerStart - 8)
  let footer ← (Compact.encodeAnnotated annotation footerLimit input.rowCount indexes).mapError Error.compact
  let data := Bytes.ofList (chunks.flatMap (fun chunk => chunk.page.wire.toList))
  let bytes := (Footer.magic.append data).append footer
  let bytes := (bytes.append (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic
  return ⟨bytes, ⟨footerStart, footerStart + footer.length⟩, Compact.metadata input.rowCount indexes, chunks⟩

def assemble (limits : Limits) (input : Input) : Except Error Encoded :=
  assembleAnnotated .unannotated limits input

/-- Check the recovered absolute interval, single page and exact body slice. -/
def Chunk.Checked (limits : Limits) (file : Bytes) (footerStart rows : Nat) (chunk : Chunk) : Prop :=
  Page.columnSpan footerStart (chunk.index.metadata rows).metadata = some chunk.index.span ∧
    Page.readChunk limits.pageReader file chunk.index.span = .ok [chunk.frame] ∧
    Footer.fileBytes file chunk.frame.payload.start chunk.frame.payload.stop = chunk.page.body

instance (limits : Limits) (file : Bytes) (footerStart rows : Nat) (chunk : Chunk) :
    Decidable (chunk.Checked limits file footerStart rows) := by
  unfold Chunk.Checked
  infer_instance

def Encoded.Checked (limits : Limits) (rows : Nat) (output : Encoded) : Prop :=
  output.bytes.length ≤ limits.maxFileBytes ∧ output.bytes.length < 2 ^ 63 ∧
    output.footer.start = 4 + (output.chunks.map (fun chunk => chunk.page.wire.length)).sum ∧
    Footer.readFooter limits.footer output.bytes = .ok (output.footer, output.metadata) ∧
    Footer.validate output.footer.start 2 output.metadata = .ok () ∧
    (∀ chunk ∈ output.chunks, chunk.Checked limits output.bytes output.footer.start rows)

instance (limits : Limits) (rows : Nat) (output : Encoded) : Decidable (output.Checked limits rows) := by
  unfold Encoded.Checked
  infer_instance

/-- Check the file's physical footer and chunk index. Callers using an
annotation check its logical round trip with the corresponding reader. -/
def emitAnnotated (annotation : Compact.LeafAnnotation) (limits : Limits) (input : Input) :
    Except Error Encoded :=
  if input.Valid limits then do
    let output ← assembleAnnotated annotation limits input
    if output.Checked limits input.rowCount then return output else throw .invariant
  else .error .schemaOrCount

/-- Return a complete file after checked recovery of its footer and chunk index. -/
def emit (limits : Limits) (input : Input) : Except Error Encoded :=
  emitAnnotated .unannotated limits input

/-- A layout covers the data area in schema order with adjacent page extents. -/
def Contiguous (start : Nat) : List Chunk → Nat → Prop
  | [], stop => start = stop
  | chunk :: rest, stop => chunk.start = start ∧ Contiguous chunk.stop rest stop

end Silmaril.Formats.Parquet.FlatInt32Writer
