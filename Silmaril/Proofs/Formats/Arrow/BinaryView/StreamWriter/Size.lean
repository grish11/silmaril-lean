module

public import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Defs
import Silmaril.Formats.Arrow.Writer.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Arrow.BinaryView.StreamWriter

open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.BinaryView.StreamWriter.Wire
open Silmaril.Formats.Arrow.MetadataWriter.Wire

private theorem appendLen (first second : KBytes) :
    (first ++ second).len = first.len + second.len := rfl

private theorem zerosLen (size : Nat) : (KBytes.zeros size).len = size := rfl

theorem schema_extent (field : BinaryView.Schema.Field) :
    (schema field).len = schemaSize field := by
  have nameSize : field.name.toByteArray.data.toList.length = field.name.utf8ByteSize := rfl
  simp only [schema, schemaSize, messagePrefix, schemaPayloadOf, fieldOffsets, fieldFragment,
    pad, words, longs, Writer.emitWords_length, appendLen, zerosLen, List.length_cons,
    List.length_nil, List.foldr_cons, List.foldr_nil, List.length_map, nameSize]
  have fragment : 4 * 7 + (4 * 5 + (4 * 1 + (1 * field.name.utf8ByteSize + 1))) =
      53 + field.name.utf8ByteSize := by omega
  rw [fragment]
  change 48 + (24 + (0 + (53 + field.name.utf8ByteSize +
    Writer.padding (53 + field.name.utf8ByteSize) + 0))) = _
  omega

private theorem descriptorWords (buffers : List Buffer) :
    (buffers.flatMap (fun buffer => [buffer.offset, buffer.length])).length =
      2 * buffers.length := by
  induction buffers with
  | nil => rfl
  | cons buffer rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    omega

theorem recordBatch_extent (node : FieldNode) (buffers : List Buffer) (count bodyLength : Nat) :
    (recordBatch node buffers count bodyLength).len = recordBatchSize buffers.length := by
  simp only [recordBatch, recordBatchSize, messagePrefix, words, longs, Writer.emitWords_length,
    appendLen, List.length_cons, List.length_nil, descriptorWords]
  omega

end Silmaril.Proofs.Formats.Arrow.BinaryView.StreamWriter
