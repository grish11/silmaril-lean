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

theorem readFields_sound {first : UInt8} {rest body : List UInt8} {header : Header}
    (success : readFields first rest = .ok (header, body)) :
    ∃ bytes, first :: rest = bytes ++ body ∧ header.WireFor (first.toNat % 4) bytes := by
  simp only [readFields] at success
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
    first, rest.take size, rfl, rfl, (format_code (Nat.mod_lt _ (by decide))).symm,
    headerSize, rfl, rfl⟩

theorem readHeader_sound {input body : List UInt8} {header : Header}
    (success : readHeader input = .ok (header, body)) :
    ∃ bytes, input = bytes ++ body ∧ header.Wire bytes := by
  cases input with
  | nil => cases success
  | cons first rest =>
    simp only [readHeader] at success
    split at success
    · rename_i fresh
      obtain ⟨bytes, shape, wire⟩ := readFields_sound success
      exact ⟨bytes, shape, by simpa only [Header.Wire, fresh] using wire⟩
    · cases success

theorem cutEnvelope_sound {limits : Limits} {header : Header} {body : List UInt8} {envelope : Envelope}
    (success : cutEnvelope limits header body = .ok envelope) :
    envelope.header = header ∧ body = envelope.body ++ envelope.rest ∧
      envelope.body.length = header.compressed ∧ header.extent ≤ limits.inputCap ∧
      header.regenerated ≤ limits.outputCap := by
  simp only [cutEnvelope] at success
  split at success
  · cases success
  rename_i inputFits
  split at success
  · cases success
  rename_i outputFits
  split at success
  · cases success
  rename_i exactBody
  cases success
  exact ⟨rfl, (List.take_append_drop _ _).symm, Classical.not_not.mp exactBody,
    Nat.le_of_not_gt inputFits, Nat.le_of_not_gt outputFits⟩

theorem readStreams_sound {limits : Limits} {header : Header} {declared : Nat} {input : List UInt8}
    {table : SingleStream.Table} {literals : List UInt8}
    (success : readStreams limits header declared input table = .ok literals) :
    StreamsWire header table declared input literals ∧
      literals.length = header.regenerated := by
  unfold readStreams at success
  split at success
  · rename_i single
    cases decode : SingleStream.Internal.readStream table header.regenerated input with
    | error reason => simp [decode, Except.mapError] at success
    | ok out =>
      simp only [decode, Except.mapError] at success
      cases success
      have wire := SingleStream.readStream_sound decode
      exact ⟨by simpa [StreamsWire, single, FourStream.ChunkWire] using wire, wire.1⟩
  · rename_i four
    cases decode : FourStream.decodeTable ⟨limits.inputCap, limits.outputCap⟩ table
        declared header.regenerated input with
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
    cases cut : cutEnvelope limits header body with
    | error reason => simp [LiteralSection.read, parsed, cut, bind, Except.bind] at success
    | ok envelope =>
      cases treeRead : TreeDescription.readTable limits.tree envelope.body with
      | error reason => simp [LiteralSection.read, parsed, cut, treeRead, Except.mapError, bind, Except.bind] at success
      | ok pair =>
        obtain ⟨tree, table⟩ := pair
        cases decoded : readStreams limits header (header.compressed - tree.consumed) tree.rest table with
        | error reason =>
          simp [LiteralSection.read, parsed, cut, treeRead, decoded, Except.mapError, bind, Except.bind] at success
        | ok out =>
          simp only [LiteralSection.read, parsed, cut, treeRead, decoded, Except.mapError,
            bind, Except.bind, pure, Except.pure] at success
          cases success
          obtain ⟨headerBytes, wholeInput, headerWire⟩ := readHeader_sound parsed
          obtain ⟨_, splitBody, exactBody, inputFits, outputFits⟩ := cutEnvelope_sound cut
          obtain ⟨_, treeValid, tableWire⟩ := TreeDescription.readTable_sound treeRead
          obtain ⟨streams, count⟩ := readStreams_sound decoded
          have remaining : tree.rest.length = header.compressed - tree.consumed := by
            rw [← TreeDescription.suffix_exact treeValid.1, List.length_drop, exactBody]
          have headerLength : headerBytes.length = header.format.headerBytes := by
            obtain ⟨_, _, _, _, _, length, _, _⟩ := headerWire
            exact length
          exact ⟨⟨headerBytes, envelope.body, tree, table, wholeInput.trans (congrArg (headerBytes ++ ·) splitBody),
            headerWire, exactBody, by rw [Header.extent, headerLength, exactBody],
            treeValid, tableWire, remaining, streams⟩, inputFits, count, outputFits⟩

theorem suffix_exact {limits : Limits} {input : List UInt8} {result : Prefix}
    (wire : Wire limits input result) : input.drop result.consumed = result.rest := by
  obtain ⟨head, body, _, _, shape, _, _, consumed, _⟩ := wire
  rw [shape, consumed, ← List.length_append, ← List.append_assoc]
  exact List.drop_left

end Silmaril.Proofs.Formats.Compression.Zstd.Huffman.LiteralSection
