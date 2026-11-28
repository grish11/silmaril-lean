module

public import Silmaril.Formats.Arrow.Metadata.Defs

/-! Schema-dependent metadata checks. The body remains an opaque byte slice.
Field nodes and buffers are ordered as specified by the flat schema. -/

@[expose] public section

namespace Silmaril.Formats.Arrow

def FieldType.bufferCount : FieldType → Nat
  | .int32 => 2
  | .utf8 => 3

/-- The buffer descriptor is aligned, follows the previous descriptor, and
lies inside the declared body. Empty descriptors can share an offset. -/
def Buffer.Fits (bodyLength previousEnd : Nat) (buffer : Buffer) : Prop :=
  previousEnd ≤ buffer.offset ∧ buffer.offset % 8 = 0 ∧
    buffer.offset + buffer.length ≤ bodyLength

instance (bodyLength previousEnd : Nat) (buffer : Buffer) :
    Decidable (buffer.Fits bodyLength previousEnd) := by
  unfold Buffer.Fits
  infer_instance

def BuffersFit (bodyLength : Nat) : Nat → List Buffer → Prop
  | _, [] => True
  | previousEnd, buffer :: rest =>
    buffer.Fits bodyLength previousEnd ∧ BuffersFit bodyLength (buffer.offset + buffer.length) rest

instance instDecidableBuffersFit (bodyLength previousEnd : Nat) (buffers : List Buffer) :
    Decidable (BuffersFit bodyLength previousEnd buffers) :=
  match buffers with
  | [] => isTrue trivial
  | buffer :: rest =>
    letI := instDecidableBuffersFit bodyLength (buffer.offset + buffer.length) rest
    show Decidable (_ ∧ _) from inferInstance

def FieldNode.Fits (rowCount : Nat) (field : Field) (node : FieldNode) : Prop :=
  node.length = rowCount ∧ node.nullCount ≤ rowCount ∧
    (field.nullable = false → node.nullCount = 0)

instance (rowCount : Nat) (field : Field) (node : FieldNode) :
    Decidable (node.Fits rowCount field) := by
  unfold FieldNode.Fits
  infer_instance

def RecordBatch.Fits (fields : List Field) (bodyLength : Nat) (batch : RecordBatch) : Prop :=
  batch.nodes.length = fields.length ∧
    batch.buffers.length = (fields.map fun field => field.type.bufferCount).sum ∧
    (∀ pair ∈ fields.zip batch.nodes, pair.2.Fits batch.rowCount pair.1) ∧
    BuffersFit bodyLength 0 batch.buffers

instance (fields : List Field) (bodyLength : Nat) (batch : RecordBatch) :
    Decidable (batch.Fits fields bodyLength) := by
  unfold RecordBatch.Fits
  infer_instance

/-- A record batch with schema-dependent descriptor validation and its raw body. -/
structure BatchFrame (fields : List Field) where
  metadata : RecordBatch
  body : KBytes
  layout : metadata.Fits fields body.len

def validateBatch (fields : List Field) (metadata : RecordBatch) (body : KBytes) :
    Except Error (BatchFrame fields) :=
  if checked : metadata.Fits fields body.len then .ok ⟨metadata, body, checked⟩
  else .error (.malformed .batchLayout)

end Silmaril.Formats.Arrow
