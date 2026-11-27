module

public import Silmaril.Formats.Parquet.MixedV1Writer.Defs

/-! A fixed mixed schema with an ordered sequence of actual Parquet row groups. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.Multi

open Int32ByteArrayGroup (Field Row)
open FlatInt32Writer.Compact (ColumnIndex)

structure Group where
  integers : PlainV1Writer.Input
  octets : PlainByteArrayV1Writer.Input

structure Input where
  intField : Field
  byteField : Field
  groups : List Group

structure Limits where
  writer : MixedV1Writer.Limits
  maxGroups : Nat
  maxTotalRows : Nat

inductive Error where
  | groupLimit
  | totalRows
  | schemaOrCount
  | fileLimit
  | measure (index : Nat) (cause : MixedV1Writer.Error)
  | page (index : Nat) (cause : MixedV1Writer.Error)
  | footer (cause : FlatInt32Writer.Compact.Error)
  | extent
  | openReadback (cause : Int32ByteArrayGroup.Error)
  | groupReadback (index : Nat) (cause : Int32ByteArrayGroup.Error)
  | values (index : Nat)
  deriving DecidableEq, Repr

def Group.rowCount (group : Group) : Nat := group.integers.numValues

def Group.rows (group : Group) : List Row := group.integers.slots.zip group.octets.slots

def Input.totalRows (input : Input) : Nat := (input.groups.map Group.rowCount).sum

def Input.single (input : Input) (group : Group) : MixedV1Writer.Input :=
  ⟨input.intField.name, group.integers, input.byteField.name, group.octets⟩

def Input.Matches (input : Input) (limits : Limits) : Prop :=
  ∀ group ∈ input.groups, (input.single group).Valid limits.writer ∧
    (input.single group).intField = input.intField ∧ (input.single group).byteField = input.byteField

instance (input : Input) (limits : Limits) : Decidable (input.Matches limits) := by
  unfold Input.Matches
  infer_instance

def Limits.fileLimit (limits : Limits) : Nat := min limits.writer.maxFileBytes (2 ^ 63 - 1)

/-- Measure all pages and place both chunks of each group before creating any page bodies. -/
def place (limits : Limits) (input : Input) : Nat → Nat → List Group → Except Error (List Compact.GroupIndex)
  | _, _, [] => .ok []
  | offset, ordinal, group :: rest => do
    let intSize ← (FlatInt32Writer.measuredPage limits.writer.intPage group.integers).mapError
      (fun _ => .measure ordinal .intBudget)
    let byteSize ← (measuredBytePage limits.writer.bytePage group.octets).mapError (.measure ordinal)
    let middle := offset + intSize
    let stop := middle + byteSize
    if stop + 8 > limits.fileLimit then throw .fileLimit
    let tail ← place limits input stop (ordinal + 1) rest
    return ⟨group.rowCount, columnIndex input.intField ⟨offset, middle⟩,
      columnIndex input.byteField ⟨middle, stop⟩⟩ :: tail

structure Pages where
  index : Compact.GroupIndex
  intPage : PlainV1Writer.Encoded
  bytePage : PlainByteArrayV1Writer.Encoded

def emitPages (limits : Limits) : Nat → List Group → List Compact.GroupIndex → Except Error (List Pages)
  | _, [], [] => .ok []
  | ordinal, group :: groups, index :: indices => do
    let ints ← (PlainV1Writer.emit limits.writer.intPage group.integers).mapError
      (fun cause => .page ordinal (.intPage cause))
    let bytes ← (PlainByteArrayV1Writer.emit limits.writer.bytePage group.octets).mapError
      (fun cause => .page ordinal (.bytePage cause))
    if ints.wire.length ≠ index.ints.size ∨ bytes.wire.length ≠ index.octets.size then throw .extent
    let tail ← emitPages limits (ordinal + 1) groups indices
    return ⟨index, ints, bytes⟩ :: tail
  | _, _, _ => .error .extent

def Pages.wire (pages : Pages) : List UInt8 := pages.intPage.wire.toList ++ pages.bytePage.wire.toList

structure Encoded where
  bytes : Bytes
  footer : Footer.Span
  groups : List Pages

def Input.intIndex (input : Input) : ColumnIndex := columnIndex input.intField ⟨0, 0⟩

def Input.byteIndex (input : Input) : ColumnIndex := columnIndex input.byteField ⟨0, 0⟩

def metadata (input : Input) (groups : List Pages) : Footer.Metadata :=
  let rows := groups.map fun pages => pages.index.rows
  let metadata := groups.map fun pages =>
    let group := pages.index
    ⟨[group.ints.metadata group.rows, byteChunk group.octets group.rows],
      group.ints.size + group.octets.size, group.rows, none, none⟩
  ⟨1, [FlatInt32Writer.Compact.schemaRoot 2, input.intIndex.schema, byteSchema input.byteIndex],
    rows.sum, metadata, none⟩

/-- Two adjoining chunks per group and no gap between consecutive groups. -/
def Contiguous (start : Nat) : List Pages → Nat → Prop
  | [], stop => start = stop
  | page :: tail, stop =>
    page.index.ints.span.start = start ∧ page.index.octets.span.start = page.index.ints.span.stop ∧
      Contiguous page.index.octets.span.stop tail stop

instance instDecidableContiguous :
    (start : Nat) → (groups : List Pages) → (stop : Nat) → Decidable (Contiguous start groups stop)
  | start, [], stop => inferInstanceAs (Decidable (start = stop))
  | start, group :: rest, stop =>
    letI := instDecidableContiguous group.index.octets.span.stop rest stop
    inferInstanceAs (Decidable (group.index.ints.span.start = start ∧
      group.index.octets.span.start = group.index.ints.span.stop ∧
      Contiguous group.index.octets.span.stop rest stop))

def columnChecked (limits : PlainV1Writer.Limits) (file : Bytes) (footerStart : Nat)
    (column : Footer.ColumnMetadata) (span : Footer.Span) (page : PlainV1Writer.Encoded) : Prop :=
  let expected := frame span page
  Page.columnSpan footerStart column = some span ∧
    Page.readChunk (pageLimits limits) file span = .ok [expected] ∧
    Footer.fileBytes file expected.payload.start expected.payload.stop = page.body

instance (limits : PlainV1Writer.Limits) (file : Bytes) (footerStart : Nat)
    (column : Footer.ColumnMetadata) (span : Footer.Span) (page : PlainV1Writer.Encoded) :
    Decidable (columnChecked limits file footerStart column span page) := by
  unfold columnChecked
  infer_instance

def Encoded.Checked (output : Encoded) (limits : Limits) (input : Input) : Prop :=
  output.bytes.length ≤ limits.writer.maxFileBytes ∧ output.bytes.length < 2 ^ 63 ∧
    output.groups.map (·.index.rows) = input.groups.map Group.rowCount ∧
    Contiguous 4 output.groups output.footer.start ∧
    Footer.readFooter limits.writer.footer output.bytes = .ok (output.footer, metadata input output.groups) ∧
    ∀ pages ∈ output.groups,
      columnChecked limits.writer.intPage output.bytes output.footer.start
        (pages.index.ints.metadata pages.index.rows).metadata pages.index.ints.span pages.intPage ∧
      columnChecked limits.writer.bytePage.page output.bytes output.footer.start
        (byteChunk pages.index.octets pages.index.rows).metadata pages.index.octets.span pages.bytePage

instance (output : Encoded) (limits : Limits) (input : Input) :
    Decidable (output.Checked limits input) := by
  unfold Encoded.Checked
  infer_instance

/-- The measured data area and remaining footer cap precede page body allocation. -/
def assemble (limits : Limits) (input : Input) : Except Error Encoded := do
  let groups ← place limits input 4 0 input.groups
  let start := (groups.getLast?.map (·.octets.span.stop)).getD 4
  if start + 8 > limits.fileLimit then throw .fileLimit
  let cap := min (min limits.writer.footer.maxFooterBytes (2 ^ 32 - 1)) (limits.fileLimit - start - 8)
  let footer ← (Compact.encodeGroups cap input.intIndex input.byteIndex groups).mapError .footer
  if footer.length > cap then throw .extent
  let pages ← emitPages limits 0 input.groups groups
  let payload := Bytes.ofList (pages.flatMap Pages.wire)
  if 4 + payload.length ≠ start then throw .extent
  let bytes := (((Footer.magic.append payload).append footer).append
    (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic
  return ⟨bytes, ⟨start, start + footer.length⟩, pages⟩

/-- Compare the original group at each indexed ordinal. An empty group still
consumes an ordinal and must return exactly an empty list. -/
def checkGroups {intField byteField : Field} (limits : Int32ByteArrayGroup.Limits)
    (opened : Int32ByteArrayGroup.Checked intField byteField) : Nat → List Group → Except Error Unit
  | _, [] => .ok ()
  | ordinal, group :: rest =>
    match opened.readGroup limits ordinal with
    | .error cause => .error (.groupReadback ordinal cause)
    | .ok rows =>
      if rows = group.rows then checkGroups limits opened (ordinal + 1) rest
      else .error (.values ordinal)

def certify (limits : Limits) (input : Input) (output : Encoded) : Except Error Unit := do
  let opened ← (Int32ByteArrayGroup.openFile limits.writer.readback output.bytes
    input.intField input.byteField).mapError .openReadback
  if opened.snapshot.groupCount = input.groups.length then
    checkGroups limits.writer.readback opened 0 input.groups
  else .error .extent

/-- One bounded file, one shared schema, and one real row group per input.
A zero-length group plan is rejected. Individual groups may be empty. -/
def emit (limits : Limits) (input : Input) : Except Error Encoded :=
  if input.groups = [] ∨ input.groups.length > limits.maxGroups ∨
      input.groups.length > limits.writer.footer.compact.maxCollectionSize then .error .groupLimit
  else if input.totalRows > limits.maxTotalRows ∨ input.totalRows ≥ 2 ^ 63 then .error .totalRows
  else if input.Matches limits then do
    let output ← assemble limits input
    if output.Checked limits input then
      (certify limits input output).map (fun _ => output)
    else .error .extent
  else .error .schemaOrCount

end Silmaril.Formats.Parquet.MixedV1Writer.Multi
