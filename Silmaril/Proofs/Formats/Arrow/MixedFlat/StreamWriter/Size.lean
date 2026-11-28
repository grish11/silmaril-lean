module

public import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Defs
import Silmaril.Formats.Arrow.Writer.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.StreamWriter

open Silmaril.Formats.Arrow
open MixedFlat.StreamWriter
open MetadataWriter.Wire

private theorem appendLen (first second : KBytes) :
    (first ++ second).len = first.len + second.len := rfl

private theorem zerosLen (size : Nat) : (KBytes.zeros size).len = size := rfl

private theorem field_extent (name : String) (nullable : Bool) (tag : Nat) (kind : KBytes)
    (typeLen : kind.len = 20) :
    (fieldFragment name nullable tag kind).len = Wire.fieldSize name := by
  have nameSize : name.toByteArray.data.toList.length = name.utf8ByteSize := rfl
  simp only [fieldFragment, Wire.fieldSize, pad, words, Writer.emitWords_length, appendLen,
    zerosLen, typeLen, List.length_cons, List.length_nil, List.length_map, nameSize]
  have size : 4 * 7 + (20 + (4 * 1 + (1 * name.utf8ByteSize + 1))) =
      53 + name.utf8ByteSize := by omega
  rw [size]

private theorem pair_payload_extent (first second : KBytes) :
    (schemaPayloadOf [first, second]).len = 32 + first.len + second.len := by
  simp only [schemaPayloadOf, fieldOffsets, words, Writer.emitWords_length, appendLen, zerosLen,
    List.length_cons, List.length_nil, List.foldr_cons, List.foldr_nil]
  change 28 + (4 + (first.len + (second.len + 0))) = 32 + first.len + second.len
  omega

theorem schema_extent (schema : Schema) :
    (Wire.schemaMetadata schema).len = Wire.schemaSize schema := by
  have integer : (fieldBytes ⟨schema.intName, schema.intNullable, .int32⟩).len =
      Wire.fieldSize schema.intName := by
    apply field_extent
    exact Writer.emitWords_length 4 [halfwords 8 12, halfwords 4 8, 8, 32, 1]
  have view : (Wire.viewField schema).len = Wire.fieldSize schema.viewName := by
    apply field_extent
    exact Writer.emitWords_length 4 [halfwords 4 4, 0, 8, 0, 0]
  cases order : schema.order <;>
    simp only [Wire.schemaMetadata, appendLen, order, MixedFlat.Writer.Order.pair, pair_payload_extent,
      integer, view, Wire.schemaSize, messagePrefix, words, longs, Writer.emitWords_length,
      List.length_cons, List.length_nil] <;> omega

end Silmaril.Proofs.Formats.Arrow.MixedFlat.StreamWriter
