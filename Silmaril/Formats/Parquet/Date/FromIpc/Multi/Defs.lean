module

public import Silmaril.Formats.Parquet.Date.FromIpc.Defs

/-! # One Parquet DATE group per explicit Date32 IPC batch -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.FromIpc.Multi

open FlatInt32Writer

structure Limits where
  writer : FlatInt32Writer.Limits
  maxGroups : Nat
  maxTotalRows : Nat

inductive Error where
  | source (cause : FromIpc.Error)
  | groupLimit
  | totalRows
  | schema
  | prepare (index : Nat) (cause : FromIpc.Error)
  | measure (index : Nat) (cause : FlatInt32Writer.Error)
  | page (index : Nat) (cause : PlainV1Writer.Error)
  | fileLimit
  | footer (cause : Compact.Error)
  | extent
  | openReadback (cause : Date.Error)
  | groupReadback (index : Nat) (cause : Date.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

abbrev Batches := List Arrow.DateValues.Column

def totalRows (batches : Batches) : Nat := (batches.map List.length).sum

namespace Internal

def checkBudget (limits : Limits) (field : Arrow.DateStream.Field)
    (batches : Batches) : Except Error Unit :=
  let compact := limits.writer.footer.compact
  if batches.isEmpty then .error (.source (.batchCount 0))
  else if batches.length > limits.maxGroups || batches.length > compact.maxCollectionSize then
    .error .groupLimit
  else if totalRows batches > limits.maxTotalRows || totalRows batches ≥ 2^63 then
    .error .totalRows
  else if limits.writer.maxColumns = 0 || compact.maxCollectionSize < 2 ||
      field.name.utf8ByteSize > compact.maxBinaryBytes then .error .schema
  else .ok ()

structure Group where
  input : PlainV1Writer.Input
  rows : Nat
  size : Nat

def prepare (limits : Limits) (nullable : Bool) (batch : Arrow.DateValues.Column)
    (index : Nat) : Except Error Group := do
  let input ← (FromIpc.Internal.pageInput nullable batch).mapError (.prepare index)
  let size ← (FlatInt32Writer.measuredPage limits.writer.page input).mapError (.measure index)
  return ⟨input, batch.length, size⟩

/-- Place each measured page once, including the nonempty page header of a zero-row group. -/
def placements (start : Nat) : List Group → List (Nat × Footer.Span)
  | [] => []
  | group :: rest =>
    let stop := start + group.size
    (group.rows, ⟨start, stop⟩) :: placements stop rest

def schemaIndex (field : Arrow.DateStream.Field) : Compact.ColumnIndex :=
  ⟨field.name, field.nullable, ⟨0, 0⟩⟩

def groupIndices (field : Arrow.DateStream.Field) (groups : List Group) :
    List (Nat × List Compact.ColumnIndex) :=
  (placements 4 groups).map fun (rows, span) => (rows, [{ schemaIndex field with span }])

def fileLimit (limits : Limits) : Nat := min limits.writer.maxFileBytes (2^63 - 1)

def footerLimit (limits : Limits) (dataStop : Nat) : Nat :=
  min (min limits.writer.footer.maxFooterBytes (2^32 - 1)) (fileLimit limits - dataStop - 8)

structure Plan where
  groups : List Group
  footer : Bytes

def Plan.dataStop (plan : Plan) : Nat := 4 + (plan.groups.map (·.size)).sum

def Plan.fileSize (plan : Plan) : Nat := plan.dataStop + plan.footer.length + 8

/-- Measure pages and serialize the bounded footer before allocating any page bodies. -/
def preflight (limits : Limits) (field : Arrow.DateStream.Field)
    (batches : Batches) : Except Error Plan := do
  checkBudget limits field batches
  let groups ← batches.zipIdx.mapM fun (batch, index) => prepare limits field.nullable batch index
  let dataStop := 4 + (groups.map (·.size)).sum
  if fileLimit limits < dataStop + 8 then .error .fileLimit
  let cap := footerLimit limits dataStop
  let footer ← (Compact.encodeGroups .date cap [schemaIndex field] (groupIndices field groups)).mapError .footer
  if footer.length > cap then .error .extent else .ok ⟨groups, footer⟩

def emit (limits : Limits) (plan : Plan) : Except Error Bytes := do
  let pages ← plan.groups.zipIdx.mapM fun (group, index) =>
    (PlainV1Writer.emit limits.writer.page group.input).mapError (.page index)
  if pages.map (·.wire.length) ≠ plan.groups.map (·.size) then .error .extent
  let data := Bytes.ofList (pages.flatMap (·.wire.toList))
  let prefixBytes := (Footer.magic.append data).append plan.footer
  return (prefixBytes.append (Bytes.ofList (KBytes.unpack 4 plan.footer.length))).append Footer.magic

def readGroups (limits : Date.Limits) (checked : Date.Checked) : Except Error (List Date.RowGroup) :=
  (List.range checked.snapshot.groupCount).mapM fun index =>
    (checked.readGroup limits index).mapError (.groupReadback index)

end Internal

/-- Exact footer descriptor, group count, aggregate rows and ordered group contents. -/
def Matches (checked : Date.Checked) (groups : List Date.RowGroup)
    (field : Arrow.DateStream.Field) (batches : Batches) : Prop :=
  checked.snapshot.groupCount = batches.length ∧
    checked.snapshot.metadata.numRows = Int.ofNat (totalRows batches) ∧
    checked.binding.leaf = FromIpc.leaf field ∧
    checked.binding.annotation = .logicalAndConverted ∧
    groups.map (·.rowCount) = batches.map List.length ∧ groups.map (·.civilSlots) = batches

instance (checked : Date.Checked) (groups : List Date.RowGroup)
    (field : Arrow.DateStream.Field) (batches : Batches) :
    Decidable (Matches checked groups field batches) := by
  unfold Matches
  infer_instance

namespace Internal

def certify (limits : Date.Limits) (wire : Bytes) (field : Arrow.DateStream.Field)
    (batches : Batches) : Except Error Bytes := do
  let checked ← (Date.openChecked limits wire).mapError .openReadback
  let groups ← readGroups limits checked
  if Matches checked groups field batches then .ok wire else .error .readbackMismatch

end Internal

/-- Read through EOS before considering output. Return one checked group per
explicit batch and release the file only after complete indexed readback. -/
def convert (inputLimits : Arrow.Limits) (writerLimits : Limits)
    (readbackLimits : Date.Limits) (input : KBytes) : Except Error Bytes := do
  let source ← (Arrow.DateStream.read inputLimits input).mapError (.source ∘ .reader)
  if source.field.unit ≠ .day then .error (.source (.wrongUnit source.field.unit))
  let plan ← Internal.preflight writerLimits source.field source.batches
  let wire ← Internal.emit writerLimits plan
  Internal.certify readbackLimits wire source.field source.batches

end Silmaril.Formats.Parquet.Date.FromIpc.Multi
