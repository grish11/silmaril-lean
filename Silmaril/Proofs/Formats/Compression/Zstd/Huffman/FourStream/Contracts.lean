module

public import Silmaril.Formats.Compression.Zstd.Huffman.FourStream.Defs
import Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.Huffman.FourStream

open Silmaril.Formats.Compression.Zstd.Huffman
open Silmaril.Formats.Compression.Zstd.Huffman.FourStream
open Silmaril.Formats.Compression.Zstd.Huffman.FourStream.Internal

private theorem extents_sound {declared : Nat} {a0 a1 b0 b1 c0 c1 : UInt8}
    {body : List UInt8} {count lastCount : Nat}
    (size : body.length + 6 = declared)
    (nonzero : ¬(le16 a0 a1 = 0 ∨ le16 b0 b1 = 0 ∨ le16 c0 c1 = 0))
    (fits : 6 + le16 a0 a1 + le16 b0 b1 + le16 c0 c1 < declared) :
    ExtentsWire declared (a0 :: a1 :: b0 :: b1 :: c0 :: c1 :: body)
      ⟨⟨body.take (le16 a0 a1), count⟩,
        ⟨(body.drop (le16 a0 a1)).take (le16 b0 b1), count⟩,
        ⟨((body.drop (le16 a0 a1)).drop (le16 b0 b1)).take (le16 c0 c1), count⟩,
        ⟨((body.drop (le16 a0 a1)).drop (le16 b0 b1)).drop (le16 c0 c1), lastCount⟩⟩ := by
  let first := le16 a0 a1
  let second := le16 b0 b1
  let third := le16 c0 c1
  let left := body.drop first
  let middle := left.drop second
  have length1 : (body.take first).length = first := by
    rw [List.length_take, Nat.min_eq_left]
    change le16 a0 a1 ≤ body.length
    omega
  have length2 : (left.take second).length = second := by
    rw [List.length_take, Nat.min_eq_left]
    simp only [left, first, second, List.length_drop]
    omega
  have length3 : (middle.take third).length = third := by
    rw [List.length_take, Nat.min_eq_left]
    simp only [middle, left, first, second, third, List.length_drop]
    omega
  have length4 : (middle.drop third).length = declared - (6 + first + second + third) := by
    simp only [middle, left, first, second, third, List.length_drop]
    omega
  have covered : body.take first ++ left.take second ++ middle.take third ++ middle.drop third = body := by
    simp only [List.append_assoc, middle, left, List.take_append_drop]
  obtain ⟨firstPositive, secondPositive, thirdPositive⟩ := by
    simpa only [not_or] using nonzero
  refine ⟨a0, a1, b0, b1, c0, c1,
    congrArg (fun tail => a0 :: a1 :: b0 :: b1 :: c0 :: c1 :: tail) covered.symm,
    length1, length2, length3, length4, ?_⟩
  intro chunk member
  simp only [Split.chunks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact length1.symm ▸ Nat.pos_of_ne_zero firstPositive
  · exact length2.symm ▸ Nat.pos_of_ne_zero secondPositive
  · exact length3.symm ▸ Nat.pos_of_ne_zero thirdPositive
  · rw [show (middle.drop third).length = _ from length4]
    change 0 < declared - (6 + le16 a0 a1 + le16 b0 b1 + le16 c0 c1)
    omega

theorem split_sound {limits : Limits} {declared regenerated : Nat} {input : List UInt8}
    {parts : Split} (success : FourStream.split limits declared regenerated input = .ok parts) :
    input.length = declared ∧ declared ≤ limits.inputBytes ∧ regenerated ≤ limits.outputSymbols ∧
      ExtentsWire declared input parts ∧ CountsWire regenerated parts := by
  unfold FourStream.split at success
  split at success
  · cases success
  rename_i withinInput
  split at success
  · cases success
  split at success
  · cases success
  rename_i exactSize
  split at success
  · cases success
  rename_i withinOutput
  split at success
  · cases success
  rename_i minimum
  have size : input.length = declared := Classical.not_not.mp exactSize
  have minimumSize : 6 ≤ regenerated := Nat.le_of_not_gt minimum
  have countFits : 3 * segmentSize regenerated ≤ regenerated := by
    unfold segmentSize
    omega
  match input with
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] => cases success
  | a0 :: a1 :: b0 :: b1 :: c0 :: c1 :: body =>
    simp only at success
    split at success
    · cases success
    rename_i nonzero
    split at success
    · cases success
    rename_i extent
    simp only [List.splitAt_eq] at success
    cases success
    refine ⟨size, Nat.le_of_not_gt withinInput, Nat.le_of_not_gt withinOutput, ?_, ?_⟩
    · exact extents_sound (by simpa [List.length_cons, Nat.add_assoc] using size) nonzero
        (Nat.lt_of_not_ge extent)
    · exact ⟨minimumSize, countFits, rfl, rfl, rfl, rfl⟩

private theorem chunks_sound {table : SingleStream.Table} {index : Nat}
    {parts : List Chunk} {output : List (List UInt8)}
    (success : decodeChunks table index parts = .ok output) : ChunksWire table parts output := by
  induction parts generalizing index output with
  | nil =>
    cases success
    exact .done
  | cons chunk parts ih =>
    cases read : SingleStream.Internal.readStream table chunk.symbols chunk.bytes with
    | error reason => simp [decodeChunks, read, Except.mapError, bind, Except.bind] at success
    | ok decoded =>
      cases remain : decodeChunks table (index + 1) parts with
      | error reason => simp [decodeChunks, read, remain, Except.mapError, bind, Except.bind] at success
      | ok suffix =>
        simp only [decodeChunks, read, remain, Except.mapError, bind, Except.bind, pure, Except.pure] at success
        cases success
        exact .cons (SingleStream.readStream_sound read) (ih remain)

private theorem outputLength {table : SingleStream.Table} {parts : List Chunk} {out : List (List UInt8)}
    (wire : ChunksWire table parts out) : out.flatten.length = (parts.map Chunk.symbols).sum := by
  induction wire with
  | done => rfl
  | cons first _ ih => simp [List.flatten_cons, first.1, ih]

private theorem decodedLength {table : SingleStream.Table} {parts : Split}
    {out : List (List UInt8)} {regenerated : Nat}
    (counts : CountsWire regenerated parts) (wire : ChunksWire table parts.chunks out) :
    out.flatten.length = regenerated := by
  obtain ⟨_, sufficient, first, second, third, fourth⟩ := counts
  rw [outputLength wire]
  simp only [Split.chunks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    first, second, third, fourth]
  omega

theorem decodeTable_sound {limits : Limits} {table : SingleStream.Table}
    {declared regenerated : Nat} {input out : List UInt8}
    (success : FourStream.decodeTable limits table declared regenerated input = .ok out) :
    input.length = declared ∧ declared ≤ limits.inputBytes ∧
      out.length = regenerated ∧ regenerated ≤ limits.outputSymbols ∧
      DecodedWire table declared regenerated input out := by
  cases partition : FourStream.split limits declared regenerated input with
  | error reason => simp [FourStream.decodeTable, partition, bind, Except.bind] at success
  | ok parts =>
    cases decoded : decodeChunks table 1 parts.chunks with
    | error reason => simp [FourStream.decodeTable, partition, decoded, bind, Except.bind, Except.map] at success
    | ok output =>
      simp only [FourStream.decodeTable, partition, decoded, bind, Except.bind, Except.map] at success
      cases success
      obtain ⟨extent, inputFits, outputFits, bytes, counts⟩ := split_sound partition
      have wire := chunks_sound decoded
      exact ⟨extent, inputFits, decodedLength counts wire, outputFits, parts, output, bytes, counts, wire, rfl⟩

theorem decode_sound {limits : Limits} {treeLimits : DirectWeights.Limits} {tree : DirectWeights.Tree}
    {declared regenerated : Nat} {input out : List UInt8}
    (success : FourStream.decode limits treeLimits tree declared regenerated input = .ok out) :
    input.length = declared ∧ declared ≤ limits.inputBytes ∧
      out.length = regenerated ∧ regenerated ≤ limits.outputSymbols ∧
      tree.Valid treeLimits ∧ ∃ parts table output, ExtentsWire declared input parts ∧
        CountsWire regenerated parts ∧ SingleStream.TableWire tree table ∧
        ChunksWire table parts.chunks output ∧ out = output.flatten := by
  cases partition : FourStream.split limits declared regenerated input with
  | error reason => simp [FourStream.decode, partition, bind, Except.bind] at success
  | ok parts =>
    cases built : SingleStream.build treeLimits tree with
    | error reason => simp [FourStream.decode, partition, built, Except.mapError, bind, Except.bind] at success
    | ok table =>
      cases decoded : decodeChunks table 1 parts.chunks with
      | error reason =>
        simp [FourStream.decode, partition, built, decoded, Except.mapError, bind, Except.bind] at success
      | ok output =>
        simp only [FourStream.decode, partition, built, decoded, Except.mapError, bind, Except.bind,
          pure, Except.pure] at success
        cases success
        obtain ⟨extent, inputFits, outputFits, bytes, counts⟩ := split_sound partition
        obtain ⟨valid, canonical⟩ := SingleStream.build_sound built
        have wire := chunks_sound decoded
        exact ⟨extent, inputFits, decodedLength counts wire, outputFits, valid, parts, table, output, bytes, counts,
          canonical, wire, rfl⟩

end Silmaril.Proofs.Formats.Compression.Zstd.Huffman.FourStream
