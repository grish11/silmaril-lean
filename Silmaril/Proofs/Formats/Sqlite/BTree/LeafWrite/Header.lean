module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
import Silmaril.Formats.Sqlite.File.Write.Thms

public section
namespace Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite

open Silmaril.Formats Silmaril.Formats.Sqlite

private theorem get_ofList (source : List UInt8) (index : Nat) :
    (File.View.ofBytes (Bytes.ofList source)).get? index = source[index]? := by
  by_cases fits : index < source.length
  · simp only [File.View.get?, File.View.ofBytes, Bytes.length_ofList, fits, ite_true, Nat.zero_add]
    have listed : (Bytes.ofList source).data.data.toList = source := Bytes.toList_ofList source
    calc
      _ = (Bytes.ofList source).data.data[index]? := rfl
      _ = (Bytes.ofList source).data.data.toList[index]? := Array.getElem?_toList.symm
      _ = _ := by rw [listed]
  · simp [File.View.get?, File.View.ofBytes, fits]

private theorem read_field (before after : List UInt8) (value : Nat)
    (fits : value < 256 ^ 2) :
    (File.View.ofBytes (Bytes.ofList (before ++ (File.Write.be 2 value ++ after)))).be?
      before.length 2 = some value := by
  apply File.Write.be?_be_two _ _ _ fits
  intro i hi
  rw [get_ofList, List.getElem?_append_right (by omega)]
  rw [show before.length + i - before.length = i by omega]
  rw [List.getElem?_append_left (by simpa using hi)]

theorem layout_header_fields {leading page : List UInt8} {cells : List (List UInt8)}
    (accepted : BTree.LeafWrite.layout leading cells = .ok page) :
    let view := File.View.ofBytes (Bytes.ofList page)
    view.be? (leading.length + 3) 2 = some cells.length ∧
      view.be? (leading.length + 5) 2 =
        some (File.Write.pageSize - cells.flatten.length) := by
  simp only [BTree.LeafWrite.layout] at accepted
  split at accepted
  next capacity =>
    cases accepted
    let content := File.Write.pageSize - cells.flatten.length
    let used := leading.length + 8 + 2 * cells.length
    let after := [0] ++ (BTree.LeafWrite.offsets content cells).flatMap (File.Write.be 2) ++
      List.replicate (content - used) 0 ++ cells.flatten
    have countFits : cells.length < 256 ^ 2 := by
      unfold File.Write.pageSize at capacity
      omega
    have contentFits : content < 256 ^ 2 := by
      have bounded := Nat.sub_le File.Write.pageSize cells.flatten.length
      dsimp [content, File.Write.pageSize] at bounded ⊢
      omega
    have priorLength : (leading ++ ([13, 0, 0] : List UInt8)).length = leading.length + 3 := by
      simp
    have priorContentLength :
        (leading ++ [13, 0, 0] ++ File.Write.be 2 cells.length).length = leading.length + 5 := by
      simp
    constructor
    · have field := read_field (leading ++ [13, 0, 0])
          (File.Write.be 2 content ++ after) cells.length countFits
      rw [priorLength] at field
      simpa [after, content, used] using field
    · have field := read_field (leading ++ [13, 0, 0] ++ File.Write.be 2 cells.length)
          after content contentFits
      rw [priorContentLength] at field
      simpa [after, content, used] using field
  next => cases accepted

end Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite
