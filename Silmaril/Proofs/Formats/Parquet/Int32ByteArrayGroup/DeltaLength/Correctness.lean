module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.Defs
import all Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.Defs
import Silmaril.Formats.Parquet.DeltaPage.Thms
import Silmaril.Formats.Parquet.DeltaLengthByteArray.Thms
import Silmaril.Formats.Parquet.FlatColumn.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength

private theorem mapError_ok {ε δ α : Type} {input : Except ε α} {f : ε → δ} {out : α}
    (success : input.mapError f = .ok out) : input = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => cases success; rfl

theorem openFile_snapshot {limits : Limits} {input : Bytes} {int32Name byteArrayName : String}
    {checked : Checked int32Name byteArrayName} (opened : openFile limits input int32Name byteArrayName = .ok checked) :
    Snapshot.check (Failure := Unit) limits.group.snapshot input = .ok checked.snapshot ∧
    checked.snapshot.metadata.schema[checked.int32Binding.leafOrdinal]? = some checked.int32Binding.leaf ∧
    checked.snapshot.metadata.schema[checked.byteArrayBinding.leafOrdinal]? = some checked.byteArrayBinding.leaf :=
  Int32ByteArrayGroup.openFile_snapshot (mapError_ok opened)

private theorem decodePage_wire {limits : Limits} {leaf : Footer.SchemaElement}
    {metadata : Footer.ColumnMetadata} {source : Bytes} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePage limits leaf metadata frame.value (FlatColumn.frameBody source frame) = .ok slots) :
    PageWire limits metadata source frame slots := by
  unfold decodePage at read
  split at read <;> try contradiction
  rename_i params projected
  split at read <;> try contradiction
  rename_i correctTag
  have tag : params.encoding = 6 := not_not.mp correctTag
  have deltaRead := mapError_ok read
  obtain ⟨encoding, layout, page, values, selected, valid, prepared, decoded, mask, ordered⟩ :=
    DeltaPage.decode_wire_sound deltaRead
  have exactEncoding : encoding.id = 6 := selected.symm.trans tag
  cases encoding with
  | byteArray => cases exactEncoding
  | lengthByteArray =>
    have lengthRead : DeltaLengthByteArray.decode limits.delta.lengthByteArray (page.mask.count true)
        page.scalars = .ok values := mapError_ok decoded
    obtain ⟨lengths, payload, cap, wire, extent, geometry, assembled, present⟩ :=
      DeltaLengthByteArray.decode_sound lengthRead
    exact ⟨params, layout, page, values, lengths, payload, projected, tag, valid, prepared,
      mask, ordered, (DeltaPage.decode_counts deltaRead).1, cap, wire, extent, geometry, assembled, present⟩

theorem readBinary_wire {int32Name byteArrayName : String} {checked : Checked int32Name byteArrayName}
    {limits : Limits} {index : Nat} {slots : List (Option Bytes)}
    (read : readBinary checked limits index = .ok slots) : ∃ group, BinaryWire checked limits index group slots := by
  obtain ⟨group, column, chunk, frames, pages, groupAt, columnAt, path, physical, count, codec,
    span, framed, declared, callbacks, output, rows⟩ := FlatColumn.readColumn_wire read
  exact ⟨group, column, chunk, frames, pages, groupAt, columnAt, path, physical, count, codec,
    span, framed, declared, callbacks.imp (fun _ _ callback => decodePage_wire callback.1), output, rows⟩

private theorem alignment {int32Name byteArrayName : String} {checked : Checked int32Name byteArrayName}
    {limits : Limits} {index : Nat} {integers : List (Option Int32)} {bytes : List (Option Bytes)}
    (readInts : checked.readInt32 limits.group index = .ok integers)
    (readBytes : readBinary checked limits index = .ok bytes) :
    ∃ group,
      FlatColumn.ColumnWire checked.int32Binding limits.group.column
        (Int32ByteArrayGroup.decodeInt32 limits.group .required) index group integers ∧
      BinaryWire checked limits index group bytes ∧
      integers.length = group.numRows.toNat ∧ bytes.length = group.numRows.toNat := by
  obtain ⟨intGroup, intWire⟩ := FlatColumn.readColumn_wire readInts
  obtain ⟨binaryGroup, binaryWire⟩ := readBinary_wire readBytes
  have intCount : checked.snapshot.groupAt index = some intGroup ∧ integers.length = intGroup.numRows.toNat := by
    obtain ⟨_, _, _, _, groupAt, _, _, _, _, _, _, _, _, _, _, count⟩ := intWire
    exact ⟨groupAt, count⟩
  have binaryCount : checked.snapshot.groupAt index = some binaryGroup ∧ bytes.length = binaryGroup.numRows.toNat := by
    obtain ⟨_, _, _, _, groupAt, _, _, _, _, _, _, _, _, _, _, count⟩ := binaryWire
    exact ⟨groupAt, count⟩
  have same : binaryGroup = intGroup := Option.some.inj (binaryCount.1.symm.trans intCount.1)
  rw [same] at binaryWire binaryCount
  exact ⟨intGroup, intWire, binaryWire, intCount.2, binaryCount.2⟩

theorem readGroup_of_columns {int32Name byteArrayName : String} {checked : Checked int32Name byteArrayName}
    {limits : Limits} {index : Nat} {integers : List (Option Int32)} {bytes : List (Option Bytes)}
    (readInts : checked.readInt32 limits.group index = .ok integers)
    (readBytes : readBinary checked limits index = .ok bytes) :
    integers.length = bytes.length ∧ readGroup checked limits index = .ok (integers.zip bytes) := by
  obtain ⟨_, _, _, intCount, binaryCount⟩ := alignment readInts readBytes
  have equal := intCount.trans binaryCount.symm
  exact ⟨equal, by simp [readGroup, readInts, readBytes, equal]⟩

theorem readGroup_wire {int32Name byteArrayName : String} {checked : Checked int32Name byteArrayName}
    {limits : Limits} {index : Nat} {rows : List Int32ByteArrayGroup.Row}
    (read : readGroup checked limits index = .ok rows) : GroupWire checked limits index rows := by
  unfold readGroup at read
  split at read <;> try contradiction
  rename_i integers readInts
  split at read <;> try contradiction
  rename_i bytes readBytes
  obtain ⟨group, intWire, binaryWire, intCount, binaryCount⟩ := alignment readInts readBytes
  have equal := intCount.trans binaryCount.symm
  simp only [equal, ite_true, Except.ok.injEq] at read
  subst rows
  have count : (integers.zip bytes).length = group.numRows.toNat := by
    rw [List.length_zip, intCount, binaryCount, Nat.min_self]
  exact ⟨group, integers, bytes, intWire, binaryWire, readInts, readBytes, equal, count, rfl, List.unzip_zip equal⟩

end Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength
