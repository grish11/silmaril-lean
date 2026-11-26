module

public import Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection.Defs
import Silmaril.Formats.Compression.Zstd.Huffman.FourStream.Thms
import Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Thms
import Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.Huffman.LiteralSection

open Silmaril.Formats.Compression.Zstd.Huffman
open Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection
open Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection.Internal

private theorem format_code {code : Nat} (fits : code < 4) :
    (SizeFormat.decode code).code = code := by
  have cases : code = 0 ∨ code = 1 ∨ code = 2 ∨ code = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl

theorem readHeader_sound {input body : List UInt8} {header : Header}
    (success : readHeader input = .ok (header, body)) :
    ∃ bytes, input = bytes ++ body ∧ header.Wire bytes := by
  cases input with
  | nil => cases success
  | cons first rest =>
    simp only [readHeader] at success
    split at success
    · rename_i fresh
      split at success
      · cases success
      rename_i exactSize
      cases success
      let code := first.toNat / 4 % 4
      let format := SizeFormat.decode code
      let size := format.headerBytes - 1
      have tailSize : (rest.take size).length = size := Classical.not_not.mp exactSize
      have headerSize : (first :: rest.take size).length = format.headerBytes := by
        simp only [List.length_cons, tailSize]
        change format.headerBytes - 1 + 1 = format.headerBytes
        cases format <;> rfl
      exact ⟨first :: rest.take size, congrArg (first :: ·) (List.take_append_drop size rest).symm,
        first, rest.take size, rfl, fresh, (format_code (Nat.mod_lt _ (by decide))).symm,
        headerSize, rfl, rfl⟩
    · cases success

private theorem readStreams_sound {limits : Limits} {header : Header} {tree : TreeDescription.Prefix}
    {table : SingleStream.Table} {literals : List UInt8}
    (success : readStreams limits header tree table = .ok literals) :
    StreamsWire header table (header.compressed - tree.consumed) tree.rest literals ∧
      literals.length = header.regenerated := by
  unfold readStreams at success
  split at success
  · rename_i single
    cases decode : SingleStream.Internal.readStream table header.regenerated tree.rest with
    | error reason => simp [decode, Except.mapError] at success
    | ok out =>
      simp only [decode, Except.mapError] at success
      cases success
      have wire := SingleStream.readStream_sound decode
      exact ⟨by simpa [StreamsWire, single, FourStream.ChunkWire] using wire, wire.1⟩
  · rename_i four
    cases decode : FourStream.decodeTable ⟨limits.inputCap, limits.outputCap⟩ table
        (header.compressed - tree.consumed) header.regenerated tree.rest with
    | error reason => simp [decode, Except.mapError] at success
    | ok out =>
      simp only [decode, Except.mapError] at success
      cases success
      obtain ⟨_, _, length, _, wire⟩ := FourStream.decodeTable_sound decode
      exact ⟨by simpa [StreamsWire, four] using wire, length⟩

theorem read_sound {limits : Limits} {input : List UInt8} {result : Prefix}
    (success : LiteralSection.read limits input = .ok result) :
    Wire limits input result ∧ result.consumed ≤ limits.inputCap ∧
      result.literals.length = result.header.regenerated ∧ result.header.regenerated ≤ limits.outputCap := by
  cases parsed : readHeader input with
  | error reason => simp [LiteralSection.read, parsed, bind, Except.bind] at success
  | ok pair =>
    obtain ⟨header, body⟩ := pair
    simp only [LiteralSection.read, parsed, bind, Except.bind] at success
    split at success
    · cases success
    rename_i inputLimit
    split at success
    · cases success
    rename_i outputLimit
    split at success
    · cases success
    rename_i extent
    let compressed := body.take header.compressed
    have exactBody : compressed.length = header.compressed := Classical.not_not.mp extent
    cases treeRead : TreeDescription.readTable limits.tree compressed with
    | error reason => simp [compressed, treeRead, Except.mapError] at success
    | ok pair =>
      obtain ⟨tree, table⟩ := pair
      cases decoded : readStreams limits header tree table with
      | error reason => simp [compressed, treeRead, decoded, Except.mapError] at success
      | ok out =>
        simp only [compressed, treeRead, decoded, Except.mapError,
          pure, Except.pure] at success
        cases success
        obtain ⟨headerBytes, wholeInput, headerWire⟩ := readHeader_sound parsed
        obtain ⟨_, treeValid, tableWire⟩ := TreeDescription.readTable_sound treeRead
        obtain ⟨streams, count⟩ := readStreams_sound decoded
        have remaining : tree.rest.length = header.compressed - tree.consumed := by
          rw [← TreeDescription.suffix_exact treeValid.1, List.length_drop, exactBody]
        have splitInput : input = headerBytes ++ (compressed ++ body.drop header.compressed) := by
          rw [wholeInput, List.take_append_drop]
        have headerLength : headerBytes.length = header.format.headerBytes := by
          obtain ⟨_, _, _, _, _, length, _, _⟩ := headerWire
          exact length
        exact ⟨⟨headerBytes, compressed, tree, table, splitInput, headerWire, exactBody,
          by rw [headerLength, exactBody], treeValid, tableWire, remaining, streams⟩,
          Nat.le_of_not_gt inputLimit, count, Nat.le_of_not_gt outputLimit⟩

theorem suffix_exact {limits : Limits} {input : List UInt8} {result : Prefix}
    (wire : Wire limits input result) : input.drop result.consumed = result.rest := by
  obtain ⟨head, body, _, _, shape, _, _, consumed, _⟩ := wire
  rw [shape, consumed, ← List.length_append, ← List.append_assoc]
  exact List.drop_left

end Silmaril.Proofs.Formats.Compression.Zstd.Huffman.LiteralSection
