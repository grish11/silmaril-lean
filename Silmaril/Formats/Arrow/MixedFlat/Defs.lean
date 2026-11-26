module

public import Silmaril.Formats.Arrow.BinaryView.Column.Defs

/-! A checked mixed-flat V5 RecordBatch over caller-paired metadata and body slices. -/

namespace Silmaril.Formats.Arrow.MixedFlat

@[expose] public section

structure Limits where
  observation : Arrow.ObservationLimits := {}
  view : BinaryView.Column.Limits := {}
  totalDataBuffers : Nat := 4096
  deriving Repr

inductive FieldError where
  | missingNode
  | invalidNode
  | missingCount
  | missingDescriptors (expected actual : Nat)
  deriving DecidableEq, Repr

inductive PlanError where
  | field (index : Nat) (cause : FieldError)
  | excess (nodes counts descriptors : Nat)
  deriving DecidableEq, Repr

inductive ColumnError where
  | layout
  | primitive (cause : Arrow.Error)
  | view (cause : BinaryView.Column.Error)
  deriving DecidableEq, Repr

inductive Error where
  | schema (cause : Arrow.Error)
  | metadata (cause : MetadataError)
  | body (cause : Arrow.Error)
  | plan (cause : PlanError)
  | field (index : Nat) (cause : ColumnError)
  deriving DecidableEq, Repr

/-- One field owns its node and a contiguous group of descriptors. Only view
fields own a count word, and zero remains an explicit count. -/
structure Group (rows : Nat) where
  field : Field
  node : FieldNode
  count : Option Nat
  buffers : List Buffer
  rowsExact : node.length = rows
  nullsFit : node.nullCount ≤ rows ∧ (field.nullable = false → node.nullCount = 0)
  countKind : count.isSome = field.kind.isView
  width : buffers.length = field.kind.baseBuffers + count.getD 0

/-- The projections reconstruct the input lists in order. The descriptor
groups therefore cover disjoint consecutive positions in the wire vector. -/
structure Assignment (rows : Nat) (fields : List Field) (nodes : List FieldNode)
    (counts : List Nat) (buffers : List Buffer) where
  groups : List (Group rows)
  fieldsExact : groups.map Group.field = fields
  nodesExact : groups.map Group.node = nodes
  countsExact : groups.filterMap Group.count = counts
  buffersExact : groups.flatMap Group.buffers = buffers

end

private structure CountSplit (isView : Bool) (counts : List Nat) where
  count : Option Nat
  rest : List Nat
  kind : count.isSome = isView
  exactCounts : count.toList ++ rest = counts

private def splitCount : (isView : Bool) → (counts : List Nat) → Option (CountSplit isView counts)
  | false, counts => some ⟨none, counts, rfl, rfl⟩
  | true, count :: rest => some ⟨some count, rest, rfl, rfl⟩
  | true, [] => none

private theorem filterMap_cons {α β : Type} (f : α → Option β) (head : α) (rest : List α) :
    (head :: rest).filterMap f = (f head).toList ++ rest.filterMap f := by
  cases h : f head <;> simp [h]

/-- Consume one node per field and one count per view field. The failure
index is the zero-based position in the full Schema. -/
public def assign (rows : Nat) : (fields : List Field) → (nodes : List FieldNode) →
    (counts : List Nat) → (buffers : List Buffer) → Nat →
      Except PlanError (Assignment rows fields nodes counts buffers)
  | [], [], [], [], _ => .ok ⟨[], rfl, rfl, rfl, rfl⟩
  | [], nodes, counts, buffers, _ => .error (.excess nodes.length counts.length buffers.length)
  | _ :: _, [], _, _, index => .error (.field index .missingNode)
  | field :: fields, node :: nodes, counts, buffers, index => do
    if valid : node.length = rows ∧ node.nullCount ≤ rows ∧
        (field.nullable = false → node.nullCount = 0) then
      let some split := splitCount field.kind.isView counts | throw (.field index .missingCount)
      let width := field.kind.baseBuffers + split.count.getD 0
      let firstBuffers := buffers.take width
      if sized : firstBuffers.length = width then
        let rest ← assign rows fields nodes split.rest (buffers.drop width) (index + 1)
        let group : Group rows := ⟨field, node, split.count, firstBuffers, valid.1, valid.2, split.kind, sized⟩
        return ⟨group :: rest.groups,
          by simp [group, rest.fieldsExact],
          by simp [group, rest.nodesExact],
          by rw [filterMap_cons, rest.countsExact]; exact split.exactCounts,
          by simp [group, firstBuffers, rest.buffersExact]⟩
      else throw (.field index (.missingDescriptors width firstBuffers.length))
    else throw (.field index .invalidNode)

@[expose] public section

structure Plan (fields : List Field) (metadata : Metadata) (body : KBytes) where
  assignment : Assignment metadata.batch.rowCount fields metadata.batch.nodes metadata.counts metadata.batch.buffers
  source : body.wf = true
  extent : metadata.bodyLength = body.len
  ordered : BuffersFit body.len 0 metadata.batch.buffers

/-- Before any physical slice or value allocation, check the body, the row
and cell budgets, exact vector assignment and the global descriptor order. -/
def bindBatch (limits : Limits) (fields : List Field) (metadata : Metadata) (body : KBytes) :
    Except Error (Plan fields metadata body) := do
  let ipc := limits.observation.ipc
  if wf : body.wf = true then
    if extent : metadata.bodyLength = body.len then
      if body.len % 8 ≠ 0 then throw (.body (.malformed .bodyLength))
      if body.len > ipc.bodyBytes then throw (.body (.limit .bodyBytes))
      if fields.length > ipc.fields then throw (.body (.limit .fields))
      if metadata.batch.rowCount > ipc.rows then throw (.body (.limit .rows))
      (Body.checkBudget limits.observation fields.length metadata.batch.rowCount).mapError .body
      let assigned ← (assign metadata.batch.rowCount fields metadata.batch.nodes metadata.counts
        metadata.batch.buffers 0).mapError .plan
      if ordered : BuffersFit body.len 0 metadata.batch.buffers then
        return ⟨assigned, wf, extent, ordered⟩
      else throw (.body (.malformed .batchLayout))
    else throw (.body (.malformed .bodyLength))
  else throw (.body (.malformed .source))

inductive Column where
  | primitive (values : Arrow.Column)
  | binaryView (values : List (Option KBytes))
  | utf8View (values : List (Option String))

structure Observed where
  rowCount : Nat
  columns : List (Field × Column)

/-- Dispatch just the descriptors assigned to this field. -/
def readGroup (limits : BinaryView.Column.Limits) (body : KBytes) {rows : Nat} (group : Group rows) :
    Except ColumnError Column := do
  match group.field.kind with
  | .primitive kind =>
    let some (buffers, []) := Body.nextColumn body kind group.buffers | throw .layout
    return .primitive (← (Body.readColumn group.node buffers).mapError .primitive)
  | .view kind =>
    let validity :: views :: data := group.buffers | throw .layout
    let buffers : BinaryView.Column.Buffers := ⟨Body.sliceBuffer body validity,
      ⟨Body.sliceBuffer body views, data.toArray.map (Body.sliceBuffer body)⟩⟩
    match kind with
    | .binary => return .binaryView (← (BinaryView.Column.readBinary limits group.node
        group.field.nullable buffers).mapError .view)
    | .utf8 => return .utf8View (← (BinaryView.Column.readUtf8 limits group.node
        group.field.nullable buffers).mapError .view)

def readGroups (limits : BinaryView.Column.Limits) (body : KBytes) {rows : Nat} :
    Nat → List (Group rows) → Except Error (List (Field × Column))
  | _, [] => .ok []
  | index, group :: groups => do
    let column ← (readGroup limits body group).mapError (.field index)
    let rest ← readGroups limits body (index + 1) groups
    return (group.field, column) :: rest

/-- Decode a standalone mixed-flat RecordBatch. The caller supplies the
Schema, RecordBatch metadata, and immutable body as one pairing. -/
def readBatch (limits : Limits) (schemaMetadata recordMetadata body : KBytes) : Except Error Observed := do
  let ipc := limits.observation.ipc
  let fields ← (readSchema ipc schemaMetadata).mapError .schema
  let metadata ←
    (readMetadata ipc limits.view.dataBuffers limits.totalDataBuffers fields recordMetadata).mapError .metadata
  let plan ← bindBatch limits fields metadata body
  let columns ← readGroups limits.view body 0 plan.assignment.groups
  return ⟨metadata.batch.rowCount, columns⟩

end

end Silmaril.Formats.Arrow.MixedFlat
