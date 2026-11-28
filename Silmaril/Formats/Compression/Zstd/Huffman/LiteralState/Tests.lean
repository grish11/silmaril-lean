module

import Silmaril.Formats.Compression.Zstd.Huffman.LiteralState.Thms
meta import Silmaril.Formats.Compression.Zstd.Huffman.LiteralState.Defs

namespace Silmaril.Formats.Compression.Zstd.Huffman.LiteralState

private def limits : LiteralSection.Limits := ⟨131072, 131072, ⟨128, ⟨256, 11⟩⟩⟩
private def empty := State.empty limits.tree
private def newTree : List UInt8 := [0x32, 0xc0, 0, 0x80, 0x10, 0x0b]
private def replacement : List UInt8 := [0x32, 0xc0, 0, 0x81, 0x01, 0x0b]
private def treelessFour : List UInt8 := [0x67, 0x80, 0x02, 1, 0, 1, 0, 1, 0, 5, 6, 7, 1]
private def suffix : List UInt8 := [0, 255]

private def exercise : Except Error Bool := do
  let installed ← read limits empty (newTree ++ suffix)
  let replacementFailed := match read limits installed.next (replacement.take 5 ++ [0]) with
    | .error (.compressed (.single .badEndMarker)) => true
    | _ => false
  let raw ← read limits installed.next [8, 97, 0]
  let rle ← read limits raw.next [25, 98, 0]
  let reused ← read limits rle.next (treelessFour ++ suffix)
  let replaced ← read limits reused.next (replacement ++ suffix)
  let usedReplacement ← read limits replaced.next (treelessFour ++ suffix)
  return replacementFailed && installed.literals == .raw [0, 1, 1] && installed.consumed == 6 && installed.rest == suffix &&
    raw.literals == .raw [97] && rle.literals == .rle 3 98 && raw.consumed == 2 && rle.consumed == 2 &&
    raw.rest == [0] && rle.rest == [0] && raw.next.table == installed.next.table &&
    rle.next.table == installed.next.table && reused.next.table == installed.next.table &&
    reused.literals == .raw [0, 1, 1, 0, 1, 1] && reused.consumed == 13 && reused.rest == suffix &&
    replaced.next.table != installed.next.table && replaced.literals == .raw [1, 2, 2] &&
    usedReplacement.literals == .raw [1, 2, 2, 1, 2, 2]

#guard match exercise with | .ok result => result | .error _ => false
#guard match read limits empty treelessFour with | .error .unavailableTable => true | _ => false
#guard match read limits empty (treelessFour.take 12) with
  | .error (.compressed .truncatedBody) => true | _ => false
#guard match read limits empty (newTree.take 5 ++ [0]) with
  | .error (.compressed (.single .badEndMarker)) => true | _ => false
#guard match read { limits with inputBytes := 1 } empty [8, 97, 0] with
  | .error (.plain .inputLimit) => true | _ => false
#guard match read { limits with outputBytes := 2 } empty [25, 98, 0] with
  | .error (.plain (.literals .outputLimit)) => true | _ => false

end Silmaril.Formats.Compression.Zstd.Huffman.LiteralState
