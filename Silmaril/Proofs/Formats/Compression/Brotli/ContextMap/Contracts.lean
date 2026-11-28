module

public import Silmaril.Formats.Compression.Brotli.ContextMap.Defs
import Silmaril.Formats.Compression.Brotli.BlockTypes.Thms
import Silmaril.Formats.Compression.Brotli.Huffman.Description.Thms
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.ContextMap

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.ContextMap
open Silmaril.Formats.Compression.Brotli.ContextMap.Internal

private structure Advance (before after : LSBReader) (input used suffix : List Bool) : Prop where
  split : input = used ++ suffix
  rep : after.Rep suffix
  buffered : after.count < 8
  offset : after.totalRead = before.totalRead + used.length

private theorem Advance.trans {before middle after : LSBReader} {input a rest b suffix : List Bool}
    (first : Advance before middle input a rest) (second : Advance middle after rest b suffix) :
    Advance before after input (a ++ b) suffix := by
  refine ⟨by rw [first.split, second.split, List.append_assoc], second.rep, second.buffered, ?_⟩
  simp only [List.length_append, first.offset, second.offset]
  omega

private theorem bind_ok {α β : Type} {action : Except Error α} {next : α → Except Error β}
    {value : β} (read : (action >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases read
  | ok value => exact ⟨value, rfl, read⟩

private theorem map_ok {α ε : Type} {action : Except ε α} {f : ε → Error} {out : α}
    (read : action.mapError f = .ok out) : action = .ok out := by
  cases action <;> cases read <;> rfl

private theorem take_sound {bitLimit width value : Nat} {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (read : take bitLimit width before = .ok (value, after)) :
    value < 2 ^ width ∧ width ≤ bitLimit ∧
      ∃ suffix, Advance before after input (natBits value width) suffix := by
  unfold take at read
  split at read <;> try contradiction
  rename_i cap
  split at read <;> try contradiction
  rename_i pair actual
  cases read
  obtain ⟨suffix, split, rep', fits, offset, count'⟩ := LSBReader.readBits_sound rep count actual
  exact ⟨fits, by omega, suffix, split, rep', count' ▸ Nat.mod_lt _ (by decide),
    by simpa only [natBits_length] using offset⟩

private theorem readRle_sound {bitLimit rleMax : Nat} {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (read : readRle bitLimit before = .ok (rleMax, after)) :
    ∃ used suffix, RleWire used rleMax ∧ Advance before after input used suffix ∧ used.length ≤ bitLimit := by
  unfold readRle at read
  obtain ⟨⟨flag, cursor⟩, flagRead, next⟩ := bind_ok read
  obtain ⟨width, cap, rest, first⟩ := take_sound rep count flagRead
  simp only [] at next
  split at next
  · rename_i zero
    subst flag
    cases next
    exact ⟨[false], rest, .off, first, cap⟩
  · rename_i nonzero
    have : flag = 1 := by omega
    subst flag
    obtain ⟨⟨value, last⟩, field, done⟩ := bind_ok next
    cases done
    obtain ⟨fits, cap', suffix, second⟩ := take_sound first.rep first.buffered field
    refine ⟨_, suffix, .on fits, first.trans second, ?_⟩
    simp only [List.length_append, List.length_cons, List.length_nil, natBits_length]
    omega

private theorem readPrefix_sound {entries bitLimit : Nat} {before after : LSBReader} {input : List Bool}
    {result : Prefix} (rep : before.Rep input) (count : before.count < 8)
    (read : readPrefix entries bitLimit before = .ok (result, after)) :
    ∃ used suffix, Wire entries used result ∧ Advance before after input used suffix ∧
      used.length ≤ bitLimit := by
  unfold readPrefix at read
  obtain ⟨⟨trees, afterCount⟩, field, next⟩ := bind_ok read
  obtain ⟨countBits, rest, countWire, split, rep', count', offset, cap⟩ :=
    BlockTypes.readCount_sound rep count (map_ok field)
  have first : Advance before afterCount input countBits rest := ⟨split, rep', count', offset⟩
  simp only [] at next
  split at next
  · rename_i one
    cases next
    have exactOne : BlockTypes.CountWire countBits 1 := one ▸ countWire
    rw [BlockTypes.CountWire.bits_of_one exactOne] at first cap
    exact ⟨[false], rest, .implicit, first, cap⟩
  · rename_i many
    split at next <;> try contradiction
    rename_i extent
    obtain ⟨⟨rleMax, afterRle⟩, rleField, next⟩ := bind_ok next
    obtain ⟨⟨table, last⟩, description, done⟩ := bind_ok next
    cases done
    obtain ⟨rleBits, rest', rleWire, second, rleCap⟩ := readRle_sound first.rep first.buffered rleField
    obtain ⟨_, _, _, alphabet, tableBits, suffix, tableWire, split', rep'', count'', offset', tableCap, _⟩ :=
      Huffman.Description.read_sound second.rep second.buffered (map_ok description)
    have third : Advance afterRle last rest' tableBits suffix := ⟨split', rep'', count'', offset'⟩
    have rleOffset := second.offset
    have range := (BlockTypes.CountWire.bounds countWire).1
    refine ⟨_, suffix, .coded (by omega) (by omega) countWire rleWire tableWire alphabet,
      (first.trans second).trans third, ?_⟩
    dsimp at tableCap
    simp only [List.length_append]
    omega

theorem read_sound {kind : Kind} {types : Nat} {limits : Limits} {before after : LSBReader}
    {input : List Bool} {result : Prefix} (rep : before.Rep input) (count : before.count < 8)
    (read : read kind types limits before = .ok (result, after)) :
    1 ≤ types ∧ types ≤ 256 ∧ kind.extent types ≤ limits.entries ∧
    ∃ used suffix, Wire (kind.extent types) used result ∧ input = used ++ suffix ∧
      after.Rep suffix ∧ after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧
      used.length ≤ limits.bits := by
  unfold Formats.Compression.Brotli.ContextMap.read at read
  split at read <;> try contradiction
  rename_i typesCap
  split at read <;> try contradiction
  rename_i entriesCap
  obtain ⟨used, suffix, wire, advance, cap⟩ := readPrefix_sound rep count read
  exact ⟨by omega, by omega, by omega, used, suffix, wire,
    advance.split, advance.rep, advance.buffered, advance.offset, cap⟩

theorem Wire.coded_bounds {entries trees rleMax : Nat} {bits : List Bool}
    {table : Huffman.Description.Table} (wire : Wire entries bits (.coded entries trees rleMax table)) :
    2 ≤ trees ∧ trees ≤ 256 ∧ trees ≤ entries ∧ rleMax ≤ 16 ∧
      table.alphabetSize = trees + rleMax ∧ table.alphabetSize ≤ 272 := by
  cases wire with
  | coded many fit count rle _ alphabet =>
    have treesCap := (BlockTypes.CountWire.bounds count).2.1
    have rleCap : rleMax ≤ 16 := by cases rle <;> omega
    exact ⟨many, treesCap, fit, rleCap, alphabet, by omega⟩

end Silmaril.Proofs.Formats.Compression.Brotli.ContextMap
