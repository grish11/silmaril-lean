module

public import Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman.Defs
import Silmaril.Formats.Compression.Zstd.CheckedFrame.Thms
import Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle.Thms
import Silmaril.Formats.Compression.Zstd.CompressedBlock.Thms
import Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.CheckedFrame.Huffman

open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Compression.Zstd.Huffman
open Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman (State)
open Silmaril.Formats.Compression.Zstd.CheckedFrame (BlockHeader)
open Silmaril.Formats.Compression.Zstd.CheckedFrame.Sequences (blockLimits)
open Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman
open Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman.Internal

theorem plain_state {profile : TreeDescription.Limits} {header : Header} {commands remaining : Nat}
    {prior : State profile} {first second third : UInt8} {bytes : List UInt8} {result : BlockResult profile}
    (kind : (BlockHeader.ofBytes first second third).kind ≠ 2)
    (wire : BlockWire header commands remaining prior (first :: second :: third :: bytes) result) :
    result.next.literals = prior.literals ∧ result.next.block.tables = prior.block.tables ∧
      result.next.block.history.offsets = prior.block.history.offsets := by
  cases wire with
  | @plain _ _ _ _ out _ _ _ _ _ =>
    obtain ⟨tables, offsets, _, _⟩ := CompressedBlock.advancePlain_sound prior.block header.windowSize out
    exact ⟨rfl, tables, offsets⟩
  | compressed typed _ _ _ _ => exact False.elim (kind typed)

theorem block_history {profile : TreeDescription.Limits} {header : Header} {commands remaining : Nat}
    {prior : State profile} {input : List UInt8} {result : BlockResult profile}
    (wire : BlockWire header commands remaining prior input result) :
    let joined := prior.block.history.recent.toList ++ result.bytes
    result.next.block.history.recent.toList = joined.drop (joined.length - header.windowSize) := by
  cases wire with
  | @plain _ _ _ _ out _ _ _ _ _ =>
    exact (CompressedBlock.advancePlain_sound prior.block header.windowSize out).2.2.1
  | @compressed _ _ _ _ _ decoded _ _ _ _ payload =>
    obtain ⟨_, _, _, _, _, _, _, _, _, sequenceWire⟩ := payload
    obtain ⟨_, _, _, _, offsets, _, _, _, _, _, _, _, advanced⟩ := sequenceWire
    change decoded.next.block.history.recent.toList = _
    rw [advanced]
    exact (CheckedFrame.Rle.advance_sound prior.block.history header.windowSize decoded.bytes offsets).1

private theorem readPlain_sound {profile : TreeDescription.Limits} {header : Header} {commands remaining : Nat}
    {prior : State profile} {first second third : UInt8} {bytes : List UInt8} {result : BlockResult profile}
    (plain : (BlockHeader.ofBytes first second third).kind ≠ 2) (valid : prior.block.Valid header.windowSize)
    (success : readPlain header remaining prior (first :: second :: third :: bytes) = .ok result) :
    BlockWire header commands remaining prior (first :: second :: third :: bytes) result ∧
      result.bytes.length ≤ remaining ∧ result.next.block.Valid header.windowSize := by
  cases read : CheckedFrame.Internal.readBlock header remaining (first :: second :: third :: bytes) with
  | error reason => simp [readPlain, read, Except.mapError, bind, Except.bind] at success
  | ok got =>
    obtain ⟨last, out, rest⟩ := got
    simp only [readPlain, read, Except.mapError, bind, Except.bind, pure, Except.pure] at success
    cases success
    obtain ⟨wire, budget⟩ := CheckedFrame.readBlock_sound read
    obtain ⟨tables, offsets, _, recent⟩ := CompressedBlock.advancePlain_sound prior.block header.windowSize out
    exact ⟨.plain plain wire budget, budget, tables.symm ▸ valid.1, recent, offsets.symm ▸ valid.2.2⟩

theorem readBlock_sound {profile : TreeDescription.Limits} {header : Header} {commands remaining : Nat}
    {prior : State profile} {input : List UInt8} {result : BlockResult profile}
    (valid : prior.block.Valid header.windowSize)
    (success : readBlock header commands remaining prior input = .ok result) :
    BlockWire header commands remaining prior input result ∧
      result.bytes.length ≤ remaining ∧ result.next.block.Valid header.windowSize := by
  match input with
  | [] | [_] | [_, _] => cases success
  | first :: second :: third :: bytes =>
    simp only [readBlock] at success
    split at success
    · rename_i compressed
      split at success
      · simp [throw, bind, Except.bind] at success
      · rename_i extent
        cases splitBody : CheckedFrame.Internal.takeExact (BlockHeader.ofBytes first second third).size bytes with
        | error reason => simp [splitBody, Except.mapError, bind, Except.bind] at success
        | ok pair =>
          obtain ⟨body, rest⟩ := pair
          cases read : CompressedBlock.Huffman.decode (blockLimits header commands remaining) prior
              (BlockHeader.ofBytes first second third).size body with
          | error reason => simp [splitBody, read, Except.mapError, bind, Except.bind] at success
          | ok decoded =>
            simp only [splitBody, read, Except.mapError, bind, Except.bind, pure, Except.pure] at success
            cases success
            obtain ⟨layout, size⟩ := CheckedFrame.takeExact_sound splitBody
            obtain ⟨_, _, outputFits, nextValid, payload⟩ := CompressedBlock.Huffman.decode_sound valid.1 read
            have budgets : decoded.bytes.length ≤ min remaining (blockMaximum header) := outputFits
            rw [layout]
            exact ⟨.compressed compressed size (size ▸ Nat.le_of_not_gt extent) budgets payload,
              (Nat.le_min.mp budgets).1, nextValid⟩
    · rename_i plain
      exact readPlain_sound plain valid success

theorem readBlocks_sound {profile : TreeDescription.Limits} {header : Header} {commands fuel remaining : Nat}
    {prior : State profile} {input trailer : List UInt8} {acc returned : List (List UInt8)}
    (valid : prior.block.Valid header.windowSize)
    (success : readBlocks header commands fuel remaining prior input acc = .ok (returned, trailer)) :
    ∃ chunks final, BlocksWire header commands remaining prior input chunks trailer final ∧
      chunks.flatten.length ≤ remaining ∧ returned = acc.reverse ++ chunks ∧ final.block.Valid header.windowSize := by
  induction fuel generalizing remaining prior input trailer acc returned with
  | zero => cases success
  | succ fuel ih =>
    cases read : readBlock header commands remaining prior input with
    | error reason => simp [readBlocks, read, bind, Except.bind] at success
    | ok block =>
      obtain ⟨wire, size, nextValid⟩ := readBlock_sound valid read
      simp only [readBlocks, read, bind, Except.bind] at success
      cases last : block.last with
      | true =>
        simp only [last, ite_true, pure, Except.pure] at success
        cases success
        exact ⟨[block.bytes], block.next, .last wire last, by simpa using size, by simp, nextValid⟩
      | false =>
        simp only [last, Bool.false_eq_true, ite_false] at success
        obtain ⟨chunks, final, suffix, suffixFits, shape, finalValid⟩ := ih nextValid success
        refine ⟨block.bytes :: chunks, final, .next wire last suffix, ?_, ?_, finalValid⟩
        · simp only [List.flatten_cons, List.length_append]
          omega
        · simpa [List.reverse_cons, List.append_assoc] using shape

theorem decode_sound {limits : Limits} {input output : List UInt8}
    (success : CheckedFrame.Huffman.decode limits input = .ok output) :
    ∃ header, FrameWire limits input output header ∧ input.length ≤ limits.frame.input ∧
      output.length ≤ limits.frame.output ∧ header.windowSize ≤ limits.frame.window := by
  cases opened : CheckedFrame.Internal.openFrame limits.frame input with
  | error reason =>
    simp [CheckedFrame.Huffman.decode, opened, Except.mapError, bind, Except.bind] at success
  | ok fields =>
    obtain ⟨size, header, blocks⟩ := fields
    obtain ⟨frameData, shape, headerWire, _, inputFits, noDictionary, windowFits⟩ :=
      CheckedFrame.openFrame_sound opened
    cases read : readBlocks header limits.commandsPerBlock (size / 3) limits.frame.output
        (State.initial limits.tree) blocks [] with
    | error reason =>
      simp [CheckedFrame.Huffman.decode, opened, read, Except.mapError, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨decoded, trailer⟩ := pair
      simp only [CheckedFrame.Huffman.decode, opened, read, Except.mapError, bind, Except.bind] at success
      obtain ⟨chunks, final, wire, outputFits, decodedShape, finalValid⟩ :=
        readBlocks_sound (CompressedBlock.initial_valid header.windowSize) read
      have eq : decoded = chunks := by simpa using decodedShape
      rw [eq] at success
      cases finished : CheckedFrame.Internal.finish header chunks.flatten trailer with
      | error reason => simp [finished] at success
      | ok out =>
        simp only [finished] at success
        cases success
        obtain ⟨rfl, contentSize, trailerWire⟩ := CheckedFrame.finish_sound finished
        exact ⟨header, ⟨frameData, blocks, chunks, trailer, final, shape, headerWire, noDictionary,
          wire, finalValid, rfl, contentSize, trailerWire⟩, inputFits, outputFits, windowFits⟩

end Silmaril.Proofs.Formats.Compression.Zstd.CheckedFrame.Huffman
