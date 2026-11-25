module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.Roundtrip

public section
namespace Silmaril.Formats.Sqlite.BTree.LeafWrite.Cell

/-- Reading a materialized writer cell at offset zero recovers the exact
rowid, eleven-byte amount payload and 13-byte extent for rowids below 128. -/
theorem cell_roundtrip_small (id : Nat) (small : id < 128) (amount : Int64) :
    let cell : Cell := ⟨Int64.ofNat id, Record.Write.amount amount⟩
    let view := File.View.ofBytes (Bytes.ofList cell.bytes)
    TableLeaf.cell? view 0 =
      some ⟨Int64.ofNat id, Bytes.ofList (Record.Write.amount amount), 0, 13⟩ :=
  Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.cell_roundtrip_small id small amount

/-- The cell and row readers recover the exact typed row for every signed
amount and a rowid from zero to 127. -/
theorem row_roundtrip_small (id : Nat) (small : id < 128) (amount : Int64) :
    let cell : Cell := ⟨Int64.ofNat id, Record.Write.amount amount⟩
    let view := File.View.ofBytes (Bytes.ofList cell.bytes)
    (TableLeaf.cell? view 0).bind TableLeaf.row? =
      some ((id : Int), [.integer (Int64.ofNat id), .integer amount]) :=
  Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.row_roundtrip_small id small amount

end Silmaril.Formats.Sqlite.BTree.LeafWrite.Cell
