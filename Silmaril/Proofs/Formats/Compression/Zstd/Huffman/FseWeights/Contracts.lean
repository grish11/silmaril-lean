module

public import Silmaril.Formats.Compression.Zstd.Huffman.FseWeights.Defs
import Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix.Thms
import Silmaril.Formats.Compression.Zstd.ReverseBits.Thms
import Silmaril.Formats.Compression.Zstd.FseTable.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.Huffman.FseWeights

open Silmaril.Formats.Compression (Bit)
open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Compression.Zstd.Huffman
open Silmaril.Formats.Compression.Zstd.Huffman.FseWeights
open Silmaril.Formats.Compression.Zstd.Huffman.FseWeights.Internal
open ReverseBits (Cursor)

private theorem symbol_bound {table : FseTable.Table} {dist : FseTable.Distribution}
    (checked : table.WellFormed dist) (alphabet : dist.weights.length ≤ 12)
    {state : Nat} {row : FseTable.Row} (lookup : table.rows[state]? = some row) : row.symbol < 12 :=
  Nat.lt_of_lt_of_le (checked.2.2.1 row (List.mem_of_getElem? lookup)).1 alphabet

private theorem emit_sound {table : FseTable.Table} {dist : FseTable.Distribution}
    (checked : table.WellFormed dist) (alphabet : dist.weights.length ≤ 12)
    {cap active waiting : Nat} {cursor : Cursor} {weights : List Nat}
    (success : emit table cap active waiting cursor = .ok weights) :
    Emits table active waiting cursor.bits weights ∧ 2 ≤ weights.length ∧
      weights.length ≤ cap ∧ ∀ weight ∈ weights, weight < 12 := by
  induction cap generalizing active waiting cursor weights with
  | zero => cases success
  | succ fuel ih =>
    cases lookup : table.rows[active]? with
    | none => simp [emit, lookup, throw] at success
    | some row =>
      simp only [emit, lookup] at success
      split at success
      · rename_i short
        split at success
        · cases success
        rename_i room
        cases waitingLookup : table.rows[waiting]? with
        | none => simp [waitingLookup, throw] at success
        | some final =>
          simp only [waitingLookup, pure, Except.pure] at success
          cases success
          refine ⟨.overflow lookup (by rwa [ReverseBits.bits_length]) waitingLookup, by simp, ?_, ?_⟩
          · simp
            omega
          · simpa using ⟨symbol_bound checked alphabet lookup, symbol_bound checked alphabet waitingLookup⟩
      · rename_i enough
        cases field : ReverseBits.read row.bits cursor with
        | none => simp [field, throw] at success
        | some pair =>
          obtain ⟨extra, next⟩ := pair
          cases continued : emit table fuel waiting (row.baseline + extra) next with
          | error reason => simp [field, continued, bind, Except.bind] at success
          | ok tail =>
            simp only [field, continued, bind, Except.bind, pure, Except.pure] at success
            cases success
            obtain ⟨readBits, shape, width, value, fieldBound, _⟩ := ReverseBits.read_sound field
            obtain ⟨wire, minimum, limit, inAlphabet⟩ := ih continued
            have lengthEq : table.rows.length = 2 ^ table.log := by
              rw [checked.1, checked.2.1]
              rfl
            have stateBound :=
              (FseTable.state_bounds checked lookup fieldBound).2.2.2
            have takeEq : cursor.bits.take row.bits = readBits := by
              rw [shape, ← width]
              exact List.take_left
            have dropEq : cursor.bits.drop row.bits = next.bits := by
              rw [shape, ← width]
              exact List.drop_left
            refine ⟨.step lookup (by rw [ReverseBits.bits_length]; omega) ?_ ?_, ?_, ?_, ?_⟩
            · simpa only [takeEq, ← value, lengthEq] using stateBound
            · simpa only [takeEq, ← value, dropEq] using wire
            · simp
              omega
            · simpa using limit
            · intro weight member
              rcases List.mem_cons.mp member with same | other
              · exact same ▸ symbol_bound checked alphabet lookup
              · exact inAlphabet weight other

theorem emits_unique {table : FseTable.Table} {active waiting : Nat} {bits : List Bit}
    {left right : List Nat} (hleft : Emits table active waiting bits left)
    (hright : Emits table active waiting bits right) : left = right := by
  induction hleft generalizing right with
  | step lookup fits _ _ ih =>
    cases hright with
    | step other _ _ tail =>
      rw [lookup] at other
      cases other
      rw [ih tail]
    | overflow other short _ =>
      rw [lookup] at other
      cases other
      omega
  | overflow lookup short final =>
    cases hright with
    | step other fits _ _ =>
      rw [lookup] at other
      cases other
      omega
    | overflow other _ otherFinal =>
      rw [lookup] at other
      rw [final] at otherFinal
      cases other
      cases otherFinal
      rfl

theorem read_sound {byteLimit weightLimit : Nat} {input : List UInt8} {result : Prefix}
    (success : read byteLimit weightLimit input = .ok result) :
    Wire input result ∧ result.consumed ≤ min byteLimit 128 ∧
      2 ≤ result.weights.length ∧ result.weights.length ≤ weightCap weightLimit ∧
      ∀ weight ∈ result.weights, weight < 12 := by
  cases parsed : FsePrefix.read byteLimit input with
  | error reason => simp [FseWeights.read, parsed, Except.mapError, bind, Except.bind] at success
  | ok parsedPrefix =>
    cases emitted : emit parsedPrefix.setup.table (weightCap weightLimit) parsedPrefix.setup.states.first
        parsedPrefix.setup.states.second parsedPrefix.setup.cursor with
    | error reason => simp [FseWeights.read, parsed, emitted, Except.mapError, bind, Except.bind] at success
    | ok weights =>
      simp only [FseWeights.read, parsed, emitted, Except.mapError, bind, Except.bind, pure, Except.pure] at success
      cases success
      obtain ⟨wire, bytesBound⟩ := FsePrefix.read_sound parsed
      have checked : parsedPrefix.setup.table.WellFormed parsedPrefix.setup.counts.distribution ∧
          parsedPrefix.setup.counts.distribution.weights.length ≤ 12 := by
        obtain ⟨_, _, _, _, _, _, _, setupWire⟩ := wire
        exact ⟨setupWire.2.2.1, setupWire.1.2.1.2.2.1⟩
      obtain ⟨trace, minimum, capacity, symbols⟩ := emit_sound checked.1 checked.2 emitted
      exact ⟨⟨parsedPrefix, wire, rfl, rfl, trace⟩, bytesBound, minimum, capacity, symbols⟩

end Silmaril.Proofs.Formats.Compression.Zstd.Huffman.FseWeights
