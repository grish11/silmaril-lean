module

public import Silmaril.Formats.Compression.Zstd.RleSequences.Defs
import Silmaril.Formats.Compression.Zstd.LiteralBlock.Thms
import Silmaril.Formats.Compression.Zstd.ReverseBits.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.RleSequences

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Compression.Zstd.RleSequences
open Silmaril.Formats.Compression.Zstd.RleSequences.Internal

theorem readCommand_sound {codes : Codes} {cursor rest : ReverseBits.Cursor} {command : Sequence.Command}
    (success : readCommand codes cursor = some (command, rest)) :
    ∃ field, cursor.bits = field ++ rest.bits ∧ CommandWire codes field command := by
  cases offsetRead : ReverseBits.read codes.offset.width cursor with
  | none => simp [readCommand, offsetRead, bind, Option.bind] at success
  | some pair =>
    obtain ⟨offset, afterOffset⟩ := pair
    cases matchRead : ReverseBits.read codes.matched.width afterOffset with
    | none => simp [readCommand, offsetRead, matchRead, bind, Option.bind] at success
    | some pair =>
      obtain ⟨matched, afterMatch⟩ := pair
      cases literalRead : ReverseBits.read codes.literals.width afterMatch with
      | none => simp [readCommand, offsetRead, matchRead, literalRead, bind, Option.bind] at success
      | some pair =>
        obtain ⟨literals, afterLiteral⟩ := pair
        simp only [readCommand, offsetRead, matchRead, literalRead, bind, Option.bind]
          at success
        cases success
        obtain ⟨offsetBits, offsetShape, offsetWidth, rfl, _, _⟩ := ReverseBits.read_sound offsetRead
        obtain ⟨matchBits, matchShape, matchWidth, rfl, _, _⟩ := ReverseBits.read_sound matchRead
        obtain ⟨literalBits, literalShape, literalWidth, rfl, _, _⟩ := ReverseBits.read_sound literalRead
        exact ⟨offsetBits ++ matchBits ++ literalBits,
          by simp [offsetShape, matchShape, literalShape, List.append_assoc],
          .fields offsetBits matchBits literalBits offsetWidth matchWidth literalWidth⟩

theorem readCommands_sound {codes : Codes} {count : Nat} {cursor : ReverseBits.Cursor}
    {acc out : List Sequence.Command} (success : readCommands codes count cursor acc = .ok out) :
    ∃ commands, out = acc.reverse ++ commands ∧ commands.length = count ∧
      CommandsWire codes cursor.bits commands := by
  induction count generalizing cursor acc with
  | zero =>
    simp only [readCommands] at success
    split at success
    · rename_i finished
      cases success
      refine ⟨[], by simp, rfl, ?_⟩
      rw [(ReverseBits.isEmpty_iff cursor).mp finished]
      exact .nil
    · cases success
  | succ count ih =>
    cases next : readCommand codes cursor with
    | none => simp [readCommands, next] at success
    | some pair =>
      obtain ⟨command, rest⟩ := pair
      simp only [readCommands, next] at success
      obtain ⟨field, bitsShape, commandWire⟩ := readCommand_sound next
      obtain ⟨commands, outputShape, length, remainingWire⟩ := ih success
      refine ⟨command :: commands, by simpa [List.reverse_cons, List.append_assoc] using outputShape,
        by simp [length], ?_⟩
      rw [bitsShape]
      exact .cons commandWire remainingWire

theorem payloadWidth {codes : Codes} {bits : List Bit} {commands : List Sequence.Command}
    (wire : CommandsWire codes bits commands) :
    bits.length = commands.length * (codes.offset.width + codes.matched.width + codes.literals.width) := by
  induction wire with
  | nil => simp
  | cons command _ ih =>
    cases command with
    | fields offset matched literals offsetWidth matchWidth literalWidth =>
      simp only [List.length_append, offsetWidth, matchWidth, literalWidth, ih, List.length_cons, Nat.succ_mul]
      omega

private theorem readRle_sound {count : Nat} {input : List UInt8} {commands : List Sequence.Command}
    (success : readRle count input = .ok commands) :
    ∃ (literal offset matched : UInt8) (stream : List UInt8) (cursor : ReverseBits.Cursor) (codes : Codes),
      input = [0x54, literal, offset, matched] ++ stream ∧ commands.length = count ∧
      tables literal offset matched = .ok codes ∧ ReverseBits.StartWire stream cursor ∧
      CommandsWire codes cursor.bits commands := by
  cases input with
  | nil => cases success
  | cons mode body =>
    simp only [readRle] at success
    split at success
    · simp [throw, bind, Except.bind] at success
    · split at success
      · simp [throw, bind, Except.bind] at success
      · rename_i modeMatches
        have modeEq : mode = 0x54 := Decidable.not_not.mp modeMatches
        match body with
        | [] | [_] | [_, _] => simp [throw] at success
        | literal :: offset :: matched :: stream =>
          cases parsed : tables literal offset matched with
          | error err => simp [parsed, bind, Except.bind] at success
          | ok codes =>
            cases started : ReverseBits.start stream with
            | none => simp [parsed, started, throw, bind, Except.bind] at success
            | some cursor =>
              simp only [parsed, started, bind, Except.bind] at success
              obtain ⟨out, shape, length, wire⟩ := readCommands_sound success
              have outEq : commands = out := by simpa using shape
              subst commands
              exact ⟨literal, offset, matched, stream, cursor, codes, by rw [modeEq]; rfl,
                length, parsed, ReverseBits.start_sound started, wire⟩

theorem decode_sound {limits : Limits} {input : List UInt8} {commands : List Sequence.Command}
    (success : decode limits input = .ok commands) :
    SectionWire input commands ∧ input.length ≤ limits.inputCapacity ∧ commands.length ≤ limits.commands := by
  simp only [RleSequences.decode] at success
  split at success
  · simp [throw, bind, Except.bind] at success
  · rename_i inputFits
    cases parsed : LiteralBlock.readSequenceCount input with
    | error err => simp [parsed, Except.mapError, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨count, rest⟩ := pair
      obtain ⟨encoded, shape, countWire⟩ := LiteralBlock.readSequenceCount_sound parsed
      simp only [parsed, Except.mapError, bind, Except.bind] at success
      split at success
      · simp [throw] at success
      · rename_i countFits
        split at success
        · rename_i zero
          cases rest with
          | cons byte tail => cases success
          | nil =>
            cases success
            exact ⟨.zero (by simpa [shape, zero] using countWire), Nat.le_of_not_gt inputFits, by simp⟩
        · rename_i notZero
          obtain ⟨literal, offset, matched, stream, cursor, codes, restShape, length, tableWire,
            started, commandWire⟩ := readRle_sound success
          refine ⟨?_, Nat.le_of_not_gt inputFits, length ▸ Nat.le_of_not_gt countFits⟩
          rw [shape, restShape, ← List.append_assoc]
          exact .rle (length ▸ countWire) (by omega) tableWire started commandWire

end Silmaril.Proofs.Formats.Compression.Zstd.RleSequences
