module

public import Silmaril.Formats.Arrow.BinaryView.Column.Defs

/-! Bind one preselected little-endian BinaryView or Utf8View field to a
standalone V5 RecordBatch message and its body. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.Batch

inductive Error where
  | metadata (cause : MetadataError)
  | bodyLength (declared actual : Nat)
  | unalignedBodyLength (actual : Nat)
  | bodyLimit
  | malformedSource
  | invalidNode
  | invalidBuffers
  | column (cause : Column.Error)
  deriving DecidableEq, Repr

/-- The flattened physical order for one view field. -/
def descriptors {source : KBytes} {maxDataBuffers : Nat}
    (metadata : BatchMetadata source maxDataBuffers) : List Buffer :=
  metadata.validity :: metadata.views :: metadata.data.toList

structure Frame (metadataBytes body : KBytes) (maxDataBuffers : Nat) where
  metadata : BatchMetadata metadataBytes maxDataBuffers
  extent : metadata.bodyLength = body.len
  aligned : body.len % 8 = 0
  source : body.wf = true
  rows : metadata.node.length = metadata.rowCount
  layout : BuffersFit body.len 0 (descriptors metadata)

/-- Validate all descriptors against the actual body before taking any
slice. The caller supplies the admitted view profile and nullability. -/
def bindBuffers (ipc : Arrow.Limits) (limits : Column.Limits) (nullable : Bool)
    (metadataBytes body : KBytes) : Except Error (Frame metadataBytes body limits.dataBuffers) := do
  let metadata ← (readBatchMetadata ipc limits.dataBuffers metadataBytes).mapError .metadata
  if extent : metadata.bodyLength = body.len then
    if body.len > ipc.bodyBytes then throw .bodyLimit
    if aligned : body.len % 8 = 0 then
      if source : body.wf = true then
        if rows : metadata.node.length = metadata.rowCount then
          if metadata.node.nullCount > metadata.rowCount ||
              (!nullable && metadata.node.nullCount != 0) then
            throw .invalidNode
          if layout : BuffersFit body.len 0 (descriptors metadata) then
            return ⟨metadata, extent, aligned, source, rows, layout⟩
          else throw .invalidBuffers
        else throw .invalidNode
      else throw .malformedSource
    else throw (.unalignedBodyLength body.len)
  else throw (.bodyLength metadata.bodyLength body.len)

/-- Extract the checked views and data descriptors in their metadata order. -/
def Frame.buffers {metadataBytes body : KBytes} {maxDataBuffers : Nat}
    (frame : Frame metadataBytes body maxDataBuffers) : Column.Buffers :=
  ⟨Body.sliceBuffer body frame.metadata.validity,
    ⟨Body.sliceBuffer body frame.metadata.views,
      frame.metadata.data.toArray.map (Body.sliceBuffer body)⟩⟩

def readBinary (ipc : Arrow.Limits) (limits : Column.Limits) (nullable : Bool)
    (metadataBytes body : KBytes) : Except Error (List (Option KBytes)) := do
  let frame ← bindBuffers ipc limits nullable metadataBytes body
  (Column.readBinary limits frame.metadata.node nullable frame.buffers).mapError .column

def readUtf8 (ipc : Arrow.Limits) (limits : Column.Limits) (nullable : Bool)
    (metadataBytes body : KBytes) : Except Error (List (Option String)) := do
  let frame ← bindBuffers ipc limits nullable metadataBytes body
  (Column.readUtf8 limits frame.metadata.node nullable frame.buffers).mapError .column

end Silmaril.Formats.Arrow.BinaryView.Batch
