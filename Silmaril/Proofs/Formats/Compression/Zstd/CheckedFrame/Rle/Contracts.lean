module

public import Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle.Defs
import Silmaril.Formats.Compression.Zstd.CheckedFrame.Thms
import Silmaril.Formats.Compression.Zstd.LiteralBlock.Thms
import Silmaril.Formats.Compression.Zstd.RleSequences.Thms
import Silmaril.Formats.Compression.Zstd.Sequence.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.CheckedFrame.Rle

open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Compression.Zstd.CheckedFrame (BlockHeader)
open Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle
open Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle.Internal

theorem advance_sound (history : History) (window : Nat) (bytes : List UInt8)
    (offsets : Sequence.RepeatOffsets) :
    (history.advance window bytes offsets).recent.toList =
      (history.recent.toList ++ bytes).drop ((history.recent.toList ++ bytes).length - window) ∧
    (history.advance window bytes offsets).recent.size ≤ window ∧
    (history.advance window bytes offsets).offsets = offsets := by
  refine ⟨?_, ?_, rfl⟩
  · simp only [History.advance, ← Array.length_toList, Array.toList_extract, List.extract,
      Array.toList_append]
    apply List.take_of_length_le
    simp only [List.length_drop, Nat.le_refl]
  · simp [History.advance]
    omega

theorem advance_suffix {history : History} {window : Nat} {previous bytes : List UInt8}
    (holds : history.recent.toList = previous.drop (previous.length - window))
    (offsets : Sequence.RepeatOffsets) :
    (history.advance window bytes offsets).recent.toList =
      (previous ++ bytes).drop ((previous ++ bytes).length - window) := by
  rw [(advance_sound history window bytes offsets).1, holds,
    ← List.drop_append_of_le_length (Nat.sub_le previous.length window), List.drop_drop]
  congr 1
  simp only [List.length_drop, List.length_append]
  omega

private theorem readCompressed_sound {header : Header} {commandLimit remaining : Nat} {history : History}
    {body : List UInt8} {result : Sequence.Result}
    (success : readCompressed header commandLimit remaining history body = .ok result) :
    CompressedWire header commandLimit history body result.bytes result.offsets ∧
      result.bytes.length ≤ remaining ∧ result.bytes.length ≤ blockMaximum header := by
  cases parsed : LiteralBlock.parseLiterals (min remaining (blockMaximum header)) body with
  | error err => simp [readCompressed, parsed, Except.mapError, bind, Except.bind] at success
  | ok fields =>
    obtain ⟨literals, sequenceBytes⟩ := fields
    cases cmds : RleSequences.decode ⟨body.length, min commandLimit (min remaining (blockMaximum header) / 3)⟩ sequenceBytes with
    | error err =>
      simp [readCompressed, parsed, cmds, Except.mapError, bind, Except.bind] at success
    | ok commands =>
      cases run : Sequence.execute ⟨header.windowSize, remaining⟩
          history.recent literals.expand history.offsets commands with
      | error err =>
        simp [readCompressed, parsed, cmds, run, Except.mapError, bind, Except.bind] at success
      | ok decoded =>
        simp only [readCompressed, parsed, cmds, run, Except.mapError, bind,
          Except.bind] at success
        cases success
        obtain ⟨literalWire, _⟩ := LiteralBlock.parseLiterals_sound parsed
        obtain ⟨sequenceWire, _, count⟩ := RleSequences.decode_sound cmds
        obtain ⟨emitted, suffix, execution, _, _, shape, _, budget, _, _⟩ := Sequence.execute_sound run
        have budget' : result.bytes.length ≤ min remaining (blockMaximum header) := budget
        exact ⟨⟨literals, sequenceBytes, commands, emitted, suffix, literalWire, sequenceWire,
          Nat.le_trans count (Nat.min_le_left _ _), execution, shape⟩, Nat.le_min.mp budget'⟩

private theorem readPlain_sound {header : Header} {commandLimit remaining : Nat} {history : History}
    {input out rest : List UInt8} {last : Bool} {offsets : Sequence.RepeatOffsets}
    (success : readPlain header remaining history input = .ok (last, out, rest, offsets)) :
    BlockWire header commandLimit history input last out rest offsets ∧ out.length ≤ remaining := by
  cases plain : CheckedFrame.Internal.readBlock header remaining input with
  | error err => simp [readPlain, plain, Except.mapError, bind, Except.bind] at success
  | ok triple =>
    obtain ⟨isLast, bytes, tail⟩ := triple
    simp only [readPlain, plain, Except.mapError, bind, Except.bind, pure, Except.pure] at success
    cases success
    obtain ⟨wire, budget⟩ := CheckedFrame.readBlock_sound plain
    exact ⟨.unchanged wire, budget⟩

theorem readBlock_sound {header : Header} {commandLimit remaining : Nat} {history : History}
    {input out rest : List UInt8} {last : Bool} {offsets : Sequence.RepeatOffsets}
    (success : readBlock header commandLimit remaining history input = .ok (last, out, rest, offsets)) :
    BlockWire header commandLimit history input last out rest offsets ∧ out.length ≤ remaining := by
  match input with
  | [] | [_] | [_, _] => cases success
  | first :: second :: third :: bytes =>
    simp only [readBlock] at success
    split at success
    · rename_i compressed
      split at success
      · simp [throw, bind, Except.bind] at success
      · rename_i extent
        cases sliced : CheckedFrame.Internal.takeExact (BlockHeader.ofBytes first second third).size bytes with
        | error err => simp [sliced, Except.mapError, bind, Except.bind] at success
        | ok pair =>
          obtain ⟨body, tail⟩ := pair
          cases executed : readCompressed header commandLimit remaining history body with
          | error err => simp [sliced, executed, Except.mapError, bind, Except.bind] at success
          | ok decoded =>
            simp only [sliced, executed, Except.mapError, bind, Except.bind, pure, Except.pure] at success
            cases success
            obtain ⟨shape, size⟩ := CheckedFrame.takeExact_sound sliced
            obtain ⟨wire, budget, blockFits⟩ := readCompressed_sound executed
            rw [shape]
            exact ⟨.compressed compressed size (size ▸ Nat.le_of_not_gt extent) blockFits wire, budget⟩
    · exact readPlain_sound success

theorem readBlocks_sound {header : Header} {commandLimit fuel remaining : Nat} {history : History}
    {input rest : List UInt8} {acc final : List (List UInt8)}
    (success : readBlocks header commandLimit fuel remaining history input acc = .ok (final, rest)) :
    ∃ chunks, BlocksWire header commandLimit history input chunks rest ∧
      chunks.flatten.length ≤ remaining ∧ final = acc.reverse ++ chunks := by
  induction fuel generalizing remaining history input rest acc final with
  | zero => cases success
  | succ fuel ih =>
    cases got : readBlock header commandLimit remaining history input with
    | error err => simp [readBlocks, got, bind, Except.bind] at success
    | ok block =>
      obtain ⟨last, out, tail, offsets⟩ := block
      obtain ⟨wire, outFits⟩ := readBlock_sound got
      simp only [readBlocks, got, bind, Except.bind] at success
      cases last with
      | true =>
        cases success
        exact ⟨[out], .last wire, by simpa using outFits, by simp⟩
      | false =>
        obtain ⟨chunks, blocks, remainingFits, shape⟩ := ih success
        refine ⟨out :: chunks, .next wire blocks, ?_, ?_⟩
        · simp only [List.flatten_cons, List.length_append]
          omega
        · simpa [List.reverse_cons, List.append_assoc] using shape

theorem decode_sound {limits : Limits} {input out : List UInt8}
    (success : CheckedFrame.Rle.decode limits input = .ok out) :
    ∃ header, FrameWire limits.commandsPerBlock input out header ∧ input.length ≤ limits.frame.input ∧
      out.length ≤ limits.frame.output ∧ header.windowSize ≤ limits.frame.window := by
  cases opened : CheckedFrame.Internal.openFrame limits.frame input with
  | error err => simp [CheckedFrame.Rle.decode, opened, Except.mapError, bind, Except.bind] at success
  | ok fields =>
    obtain ⟨size, header, blocks⟩ := fields
    obtain ⟨frameData, shape, parsed, _, inputFits, dictionary, windowFits⟩ :=
      CheckedFrame.openFrame_sound opened
    cases read : readBlocks header limits.commandsPerBlock (size / 3)
        limits.frame.output History.initial blocks [] with
    | error err => simp [CheckedFrame.Rle.decode, opened, read, Except.mapError, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨decoded, trailer⟩ := pair
      simp only [CheckedFrame.Rle.decode, opened, read, Except.mapError, bind, Except.bind] at success
      obtain ⟨chunks, wire, budget, decodedShape⟩ := readBlocks_sound read
      have decodedEq : decoded = chunks := by simpa using decodedShape
      rw [decodedEq] at success
      cases finished : CheckedFrame.Internal.finish header chunks.flatten trailer with
      | error err => simp [finished] at success
      | ok result =>
        simp only [finished] at success
        cases success
        obtain ⟨rfl, finalSize, trailerWire⟩ := CheckedFrame.finish_sound finished
        exact ⟨header, ⟨frameData, blocks, trailer, chunks,
          shape, parsed, dictionary, wire, rfl, finalSize, trailerWire⟩,
          inputFits, budget, windowFits⟩

end Silmaril.Proofs.Formats.Compression.Zstd.CheckedFrame.Rle
