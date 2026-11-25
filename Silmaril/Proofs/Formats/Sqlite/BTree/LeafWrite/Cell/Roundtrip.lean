module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Formats.Sqlite.Record.Write.Thms

public section
namespace Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell

open Silmaril.Formats Silmaril.Formats.Sqlite

private theorem encode_one_bytes (value : UInt64) (one : value.toNat < 128) :
    (Varint.encode value).toList = [UInt8.ofNat value.toNat] := by
  have short : value.toNat < 2 ^ 56 := by omega
  unfold Varint.encode
  rw [ite_eq_left short, Varint.seven, ite_eq_left one]
  have small := Nat.lt_trans one (by decide : 128 < 256)
  simp [Nat.mod_eq_of_lt one, Nat.mod_eq_of_lt small]

private theorem readNat?_encode_one (view : File.View) (offset : Nat) (value : UInt64)
    (one : value.toNat < 128)
    (byte : view.get? offset = (Varint.encode value).toList[0]?) :
    Varint.readNat? view offset = some (value.toNat, offset + 1) := by
  rw [encode_one_bytes value one] at byte
  have small := Nat.lt_trans one (by decide : 128 < 256)
  have byteValue : (UInt8.ofNat value.toNat).toNat = value.toNat :=
    UInt8.toNat_ofNat_of_lt' small
  rw [Varint.readNat?, Varint.readAux?, byte]
  change (if (UInt8.ofNat value.toNat).toNat < 128
          then some (0 * 128 + (UInt8.ofNat value.toNat).toNat % 128, offset + 1)
          else Varint.readAux? view 8 (offset + 1)
            (0 * 128 + (UInt8.ofNat value.toNat).toNat % 128)) = _
  rw [byteValue, ite_eq_left one, Nat.mod_eq_of_lt one, Nat.zero_mul, Nat.zero_add]

private theorem read?_encode_one (view : File.View) (offset : Nat) (value : UInt64)
    (one : value.toNat < 128)
    (byte : view.get? offset = (Varint.encode value).toList[0]?) :
    Varint.read? view offset = some (value, offset + 1) := by
  rw [Varint.read?, readNat?_encode_one view offset value one byte]
  simp

private theorem writer_bytes (id : Nat) (small : id < 128) (amount : Int64) :
    (BTree.LeafWrite.Cell.bytes ⟨Int64.ofNat id, Record.Write.amount amount⟩) =
      [11, UInt8.ofNat id] ++ Record.Write.amount amount := by
  have idNat : (UInt64.ofNat id).toNat = id := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : id < 2 ^ 64)]
  have one := encode_one_bytes (UInt64.ofNat id) (idNat.symm ▸ small)
  have size := encode_one_bytes 11 (by decide)
  unfold BTree.LeafWrite.Cell.bytes
  simp [Record.Write.amount_length, size, one, idNat]

theorem cell_roundtrip_small (id : Nat) (small : id < 128) (amount : Int64) :
    let cell : BTree.LeafWrite.Cell := ⟨Int64.ofNat id, Record.Write.amount amount⟩
    let view := File.View.ofBytes (Bytes.ofList cell.bytes)
    TableLeaf.cell? view 0 =
      some ⟨Int64.ofNat id, Bytes.ofList (Record.Write.amount amount), 0, 13⟩ := by
  dsimp only
  rw [writer_bytes id small amount]
  let source := Bytes.ofList ([11, UInt8.ofNat id] ++ Record.Write.amount amount)
  let view := File.View.ofBytes source
  have idNat : (UInt64.ofNat id).toNat = id := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : id < 2 ^ 64)]
  have sizeByte : view.get? 0 = (Varint.encode 11).toList[0]? := by
    rw [encode_one_bytes 11 (by decide)]
    rfl
  have idByte : view.get? 1 = (Varint.encode (UInt64.ofNat id)).toList[0]? := by
    rw [encode_one_bytes (UInt64.ofNat id) (idNat.symm ▸ small), idNat]
    rfl
  have sizeRead : Varint.readNat? view 0 = some (11, 1) :=
    readNat?_encode_one view 0 11 (by decide) sizeByte
  have keyRead : Varint.read? view 1 = some (UInt64.ofNat id, 2) :=
    read?_encode_one view 1 (UInt64.ofNat id) (idNat.symm ▸ small) idByte
  have srcLength : source.length = 13 := by simp [source]
  let payload : File.View := ⟨source, 2, 11, by omega⟩
  have sub : view.sub? 2 11 = some payload := by
    unfold view File.View.sub? File.View.ofBytes
    rw [dite_eq_left (by omega : 2 + 11 ≤ source.length)]
  have extracted : payload.materialize = Bytes.ofList (Record.Write.amount amount) := by
    change Bytes.mk (([11, UInt8.ofNat id] ++ Record.Write.amount amount).toByteArray.extract 2 13) = _
    rw [List.toByteArray_append]
    apply congrArg Bytes.mk
    apply ByteArray.extract_append_eq_right rfl
    simp
  have key : Int64.ofInt (File.signed 8 (UInt64.ofNat id).toNat) = Int64.ofNat id := by
    rw [idNat, File.signed, ite_eq_left (by omega : id < 2 ^ (8 * 8 - 1))]
    rw [Int64.ofInt_eq_ofNat]
  change TableLeaf.cell? view 0 = _
  simp only [UInt64.toNat_ofNat', Nat.reducePow] at key
  have available : 13 ≤ view.length := by
    change 13 ≤ source.length
    omega
  simp [TableLeaf.cell?, sizeRead, keyRead, sub, extracted, key, available, guard]

theorem row_roundtrip_small (id : Nat) (small : id < 128) (amount : Int64) :
    let cell : BTree.LeafWrite.Cell := ⟨Int64.ofNat id, Record.Write.amount amount⟩
    let view := File.View.ofBytes (Bytes.ofList cell.bytes)
    (TableLeaf.cell? view 0).bind TableLeaf.row? =
      some ((id : Int), [.integer (Int64.ofNat id), .integer amount]) := by
  dsimp only
  rw [cell_roundtrip_small id small amount]
  simp only [Option.bind_some, TableLeaf.row?, Record.Write.decode_amount]
  have range : (id : Int) < 2 ^ 63 := by omega
  have idExact : (Int64.ofNat id).toInt = (id : Int) := by
    rw [← Int64.ofInt_eq_ofNat]
    exact Int64.toInt_ofInt_of_le (by omega) range
  simp [idExact]

end Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell
