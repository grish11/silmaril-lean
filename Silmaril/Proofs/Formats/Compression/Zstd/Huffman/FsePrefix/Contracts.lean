module

public import Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix.Defs
import Silmaril.Formats.Compression.Zstd.FseTable.NCount.Thms
import Silmaril.Formats.Compression.Zstd.ReverseBits.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.Huffman.FsePrefix

open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix
open Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix.Internal
open FseTable
open ReverseBits (Cursor)

private theorem initialize_sound {width : Nat} {cursor rest : Cursor} {states : States}
    (success : readStates width cursor = some (states, rest)) : InitWire width cursor states rest := by
  cases first : ReverseBits.read width cursor with
  | none => simp [readStates, first, bind, Option.bind] at success
  | some firstPair =>
    obtain ⟨a, middle⟩ := firstPair
    cases second : ReverseBits.read width middle with
    | none => simp [readStates, first, second, bind, Option.bind] at success
    | some secondPair =>
      obtain ⟨b, tail⟩ := secondPair
      simp only [readStates, first, second, bind, Option.bind] at success
      cases success
      obtain ⟨bitsA, eqA, lenA, valueA, boundA, remainingA⟩ := ReverseBits.read_sound first
      obtain ⟨bitsB, eqB, lenB, valueB, boundB, remainingB⟩ := ReverseBits.read_sound second
      refine ⟨⟨bitsA, bitsB, ?_, lenA, lenB, valueA, valueB⟩, boundA, boundB, by omega⟩
      rw [eqA, eqB, List.append_assoc]

private theorem readSetup_sound {body : List UInt8} {setup : Setup}
    (success : readSetup body = .ok setup) : setup.Wire body := by
  cases checked : NCount.readTable (countLimits body.length) body with
  | error reason => simp [readSetup, checked, Except.mapError, bind, Except.bind] at success
  | ok pair =>
    obtain ⟨counts, table⟩ := pair
    cases opened : ReverseBits.start counts.rest with
    | none => simp [readSetup, checked, opened, Except.mapError, bind, Except.bind, throw] at success
    | some start =>
      cases init : readStates table.log start with
      | none => simp [readSetup, checked, opened, init, Except.mapError, bind, Except.bind, throw] at success
      | some pair =>
        obtain ⟨states, cursor⟩ := pair
        simp only [readSetup, checked, opened, init, Except.mapError, bind, Except.bind, pure, Except.pure] at success
        cases success
        obtain ⟨valid, wire, wellFormed⟩ := NCount.readTable_sound checked
        have statesWire := initialize_sound init
        have lengthEq : table.rows.length = 2 ^ table.log := by
          rw [wellFormed.1, wellFormed.2.1]
          rfl
        have logFits : table.log ≤ 6 := by
          rw [wellFormed.1]
          exact valid.2.1.2.1
        refine ⟨valid, wire, wellFormed, ?_, lengthEq ▸ statesWire.2.1,
          lengthEq ▸ statesWire.2.2.1, start, ReverseBits.start_sound opened, statesWire⟩
        rw [lengthEq]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) logFits

theorem read_sound {byteLimit : Nat} {input : List UInt8} {result : Prefix}
    (success : read byteLimit input = .ok result) :
    PrefixWire input result ∧ result.consumed ≤ min byteLimit 128 := by
  cases input with
  | nil => cases success
  | cons header input =>
    simp only [Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix.read] at success
    split at success
    · cases success
    rename_i fse
    split at success
    · cases success
    rename_i positive
    split at success
    · cases success
    rename_i cap
    split at success
    · cases success
    rename_i size
    let body := input.take header.toNat
    have sizeEq : body.length = header.toNat := Classical.not_not.mp size
    change (readSetup body).map _ = .ok result at success
    cases setup : readSetup body with
    | error reason => simp [setup, Except.map] at success
    | ok prepared =>
      simp only [setup, Except.map] at success
      cases success
      refine ⟨⟨header, body, congrArg (header :: ·) (List.take_append_drop header.toNat input).symm,
        Nat.pos_of_ne_zero positive, Nat.lt_of_not_ge fse, sizeEq, by rw [sizeEq], readSetup_sound setup⟩, ?_⟩
      change 1 + header.toNat ≤ min byteLimit 128
      exact Nat.le_min.mpr ⟨Nat.le_of_not_gt cap, by omega⟩

theorem suffix_exact {input : List UInt8} {result : Prefix} (wire : PrefixWire input result) :
    input.drop result.consumed = result.rest := by
  obtain ⟨header, body, shape, _, _, _, consumed, _⟩ := wire
  rw [shape, consumed, Nat.add_comm, ← List.length_cons]
  exact List.drop_left

end Silmaril.Proofs.Formats.Compression.Zstd.Huffman.FsePrefix
