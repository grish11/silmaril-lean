module

public import Silmaril.Formats.Compression.Brotli.Huffman.Description.Defs
import Silmaril.Formats.Compression.Brotli.Huffman.Simple.Thms
import Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths.Thms
import Silmaril.Formats.Compression.Brotli.Huffman.MainTable.Thms
import Silmaril.Formats.Compression.Brotli.Huffman.MainLengths.Thms
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Huffman.Description

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.Huffman
open Silmaril.Formats.Compression.Brotli.Huffman.Description
open Silmaril.Formats.Compression.Brotli.Huffman.Description.Internal

private theorem bind_ok {α β : Type} {action : Except Error α} {next : α → Except Error β}
    {value : β} (read : (action >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases read
  | ok value => exact ⟨value, rfl, read⟩

private theorem map_ok {α ε : Type} {action : Except ε α} {f : ε → Error} {out : α}
    (read : action.mapError f = .ok out) : action = .ok out := by
  cases action <;> cases read <;> rfl

private theorem installed_positive {lengths : List Nat} {table : Table}
    (read : ((MainTable.Internal.install lengths).map Table.canonical).mapError Error.simpleCode = .ok table) :
    ∃ codes, table = .canonical codes ∧ codes.lengths = lengths := by
  cases h : MainTable.Internal.install lengths with
  | error _ => simp [h, Except.map, Except.mapError] at read
  | ok codes =>
    simp only [h, Except.map, Except.mapError, Except.ok.injEq] at read
    refine ⟨codes, read.symm, ?_⟩
    unfold MainTable.Internal.install at h
    split at h <;> cases h <;> rfl

private theorem installSimple_sound {alphabet : Nat} {checked : Simple.Checked alphabet}
    {table : Table} (read : installSimple checked = .ok table) :
    SimpleTableWire alphabet checked.shape table := by
  obtain ⟨shape, bounded, distinct⟩ := checked
  cases shape
  case singleton only =>
    cases read
    exact ⟨bounded only (by simp [Simple.Shape.symbols]), rfl⟩
  all_goals exact installed_positive read

private theorem simple_size {alphabet : Nat} {shape : Simple.Shape} {table : Table}
    (wire : SimpleTableWire alphabet shape table) : table.alphabetSize = alphabet := by
  cases shape
  case singleton only =>
    obtain ⟨_, rfl⟩ := wire
    rfl
  all_goals
    obtain ⟨codes, rfl, lengths⟩ := wire
    simp [Table.alphabetSize, lengths, Simple.Shape.lengths]

private theorem readSimple_sound {alphabet limit : Nat} {before after : LSBReader}
    {input : List Bool} {table : Table} (rep : before.Rep input) (count : before.count < 8)
    (read : readSimple alphabet limit before = .ok (table, after)) :
    table.alphabetSize = alphabet ∧
    ∃ shape used suffix, Simple.Wire alphabet used shape ∧ SimpleTableWire alphabet shape table ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ limit := by
  unfold readSimple at read
  obtain ⟨⟨checked, cursor⟩, body, next⟩ := bind_ok read
  obtain ⟨built, installed, done⟩ := bind_ok next
  cases done
  have tableWire := installSimple_sound installed
  obtain ⟨used, suffix, w, split, rep', count', offset, fits⟩ := Simple.read_sound rep count (map_ok body)
  exact ⟨simple_size tableWire, checked.shape, used, suffix, w, tableWire, split, rep', count', offset, fits⟩

private theorem readComplex_sound {limits : MainLengths.Limits} {alphabet : Nat}
    {before after : LSBReader} {input : List Bool} {table : Table}
    (rep : before.Rep input) (count : before.count < 8)
    (read : readComplex limits alphabet before = .ok (table, after)) :
    table.alphabetSize = alphabet ∧
    ∃ used suffix, Wire alphabet used table ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ limits.bits ∧
      used.length ≤ 74 + 8 * alphabet := by
  unfold readComplex at read
  obtain ⟨⟨secondary, cursor⟩, header, next⟩ := bind_ok read
  obtain ⟨⟨codes, final⟩, body, done⟩ := bind_ok next
  cases done
  obtain ⟨pre, rest, headerWire, split, rep', count', offset, limitPre, preCap⟩ :=
    CodeLengths.read_sound rep count (map_ok header)
  obtain ⟨_, size, _, _, _, _, _, _, used, suffix, bodyWire, split', rep'', count'', offset', limitBody⟩ :=
    MainTable.read_sound rep' count' (map_ok body)
  obtain ⟨_, _, _, bodyCap⟩ := MainLengths.RunsWire.bounds bodyWire
  refine ⟨size, pre ++ used, suffix, .complex headerWire bodyWire, ?_, rep'', count'', ?_, ?_, ?_⟩
  · rw [split, split', List.append_assoc]
  · simp only [List.length_append, offset', offset]
    omega
  · dsimp at limitBody
    simp only [List.length_append]
    omega
  · simp only [List.length_append]
    omega

theorem read_sound {limits : MainLengths.Limits} {alphabet : Nat}
    {before after : LSBReader} {input : List Bool} {table : Table}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read limits alphabet before = .ok (table, after)) :
    0 < alphabet ∧ alphabet ≤ 704 ∧ alphabet ≤ limits.alphabet ∧ table.alphabetSize = alphabet ∧
    ∃ used suffix, Wire alphabet used table ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ limits.bits ∧
      used.length ≤ 74 + 8 * alphabet := by
  unfold Formats.Compression.Brotli.Huffman.Description.read at read
  split at read <;> try contradiction
  rename_i standard
  split at read <;> try contradiction
  rename_i caller
  split at read <;> try contradiction
  rename_i fits
  split at read <;> try contradiction
  rename_i selector cursor actual
  split at read
  · rename_i simple
    subst selector
    obtain ⟨remaining, split, rep', _, offset, count'⟩ := LSBReader.readBits_sound rep count actual
    obtain ⟨size, shape, used, suffix, body, installed, split', rep'', count'', offset', cap⟩ :=
      readSimple_sound rep' (count' ▸ Nat.mod_lt _ (by decide)) read
    have bound := Simple.Wire.bit_bound body (by omega)
    refine ⟨by omega, by omega, by omega, size, natBits 1 2 ++ used, suffix, .simple body installed,
      ?_, rep'', count'', ?_, ?_, ?_⟩
    · rw [split, split', List.append_assoc]
    · simp only [List.length_append, natBits_length, offset', offset]
      omega
    · simp only [List.length_append, natBits_length]
      omega
    · simp only [List.length_append, natBits_length]
      omega
  · exact ⟨by omega, by omega, by omega, readComplex_sound rep count read⟩

theorem Wire.selector {alphabet : Nat} {used : List Bool} {table : Table}
    (wire : Wire alphabet used table) :
    ∃ selector rest, used = natBits selector 2 ++ rest ∧
      ((selector = 1 ∧ ∃ shape, Simple.Wire alphabet rest shape ∧ SimpleTableWire alphabet shape table) ∨
        selector ∈ [0, 2, 3]) := by
  cases wire with
  | @simple shape body out simple installed =>
    exact ⟨1, body, rfl, .inl ⟨rfl, shape, simple, installed⟩⟩
  | @complex secondary header body codes pre _ =>
    obtain ⟨skip, _, _, bits, split, _⟩ := pre
    exact ⟨skip.count, bits ++ body, by rw [split, List.append_assoc],
      .inr (by cases skip <;> decide)⟩

end Silmaril.Proofs.Formats.Compression.Brotli.Huffman.Description
