module

public import Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths.Defs
import Silmaril.Formats.Compression.Bits.Thms
import Silmaril.Formats.Compression.Deflate.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Huffman.CodeLengths

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths
open Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths.Internal

private structure Advance (before after : Cursor) (input used suffix : List Bool) : Prop where
  split : input = used ++ suffix
  rep : after.reader.Rep suffix
  count : after.reader.count < 8
  offset : after.reader.totalRead = before.reader.totalRead + used.length
  budget : before.remaining = after.remaining + used.length

private theorem Advance.refl {cursor : Cursor} {bits : List Bool}
    (rep : cursor.reader.Rep bits) (count : cursor.reader.count < 8) :
    Advance cursor cursor bits [] bits :=
  ⟨rfl, rep, count, by simp, by simp⟩

private theorem Advance.trans {before middle after : Cursor}
    {input used suffix consumed rest : List Bool}
    (first : Advance before middle input used suffix) (second : Advance middle after suffix consumed rest) :
    Advance before after input (used ++ consumed) rest := by
  refine ⟨by rw [first.split, second.split, List.append_assoc], second.rep, second.count, ?_, ?_⟩
  · simp only [List.length_append, second.offset, first.offset]
    omega
  · simp only [List.length_append, first.budget, second.budget]
    omega

private theorem bind_ok {α β : Type} {action : Except Error α} {next : α → Except Error β}
    {value : β} (read : (action >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases read
  | ok result => exact ⟨result, rfl, read⟩

private theorem take_sound {before after : Cursor} {width value : Nat} {bits : List Bool}
    (rep : before.reader.Rep bits) (count : before.reader.count < 8)
    (read : take before width = .ok (value, after)) :
    value < 2 ^ width ∧ ∃ suffix, Advance before after bits (natBits value width) suffix := by
  unfold take at read
  split at read
  · contradiction
  · rename_i widthFits
    cases readBits : before.reader.readBits width with
    | none => simp [readBits] at read
    | some pair =>
      obtain ⟨v, reader⟩ := pair
      simp only [readBits, Except.ok.injEq, Prod.mk.injEq] at read
      obtain ⟨rfl, rfl⟩ := read
      obtain ⟨suffix, consumed, rep', valueBound, offset, count'⟩ :=
        LSBReader.readBits_sound rep count readBits
      refine ⟨valueBound, suffix, consumed, rep', ?_, ?_, ?_⟩
      · exact count' ▸ Nat.mod_lt _ (by decide)
      · simpa only [natBits_length] using offset
      · simp only [natBits_length]
        omega

private theorem select_sound {selector : Nat} {skip : Skip}
    (read : select selector = .ok skip) : selector = skip.count := by
  unfold select at read
  split at read <;> cases read <;> rfl

private theorem readLength_sound {before after : Cursor} {value : Length} {bits : List Bool}
    (rep : before.reader.Rep bits) (count : before.reader.count < 8)
    (read : readLength before = .ok (value, after)) :
    ∃ suffix, Advance before after bits value.bits suffix := by
  unfold readLength at read
  obtain ⟨⟨head, cursor⟩, headRead, next⟩ := bind_ok read
  obtain ⟨headBound, tail, first⟩ := take_sound rep count headRead
  have headCases : head = 0 ∨ head = 1 ∨ head = 2 ∨ head = 3 := by omega
  rcases headCases with rfl | rfl | rfl | rfl
  · cases next
    exact ⟨tail, first⟩
  · cases next
    exact ⟨tail, first⟩
  · cases next
    exact ⟨tail, first⟩
  · obtain ⟨⟨third, thirdCursor⟩, thirdRead, next⟩ := bind_ok next
    obtain ⟨thirdBound, thirdTail, thirdStep⟩ := take_sound first.rep first.count thirdRead
    have thirdCases : third = 0 ∨ third = 1 := by omega
    rcases thirdCases with rfl | rfl
    · cases next
      exact ⟨thirdTail, first.trans thirdStep⟩
    · obtain ⟨⟨fourth, fourthCursor⟩, fourthRead, next⟩ := bind_ok next
      obtain ⟨fourthBound, fourthTail, fourthStep⟩ := take_sound thirdStep.rep thirdStep.count fourthRead
      have fourthCases : fourth = 0 ∨ fourth = 1 := by omega
      rcases fourthCases with rfl | rfl <;> cases next <;>
        exact ⟨fourthTail, (first.trans thirdStep).trans fourthStep⟩

private theorem readLengths_sound {slots space final : Nat} {before after : Cursor}
    {lengths : List Length} {bits : List Bool}
    (rep : before.reader.Rep bits) (count : before.reader.count < 8)
    (read : readLengths slots space before = .ok (lengths, final, after)) :
    ∃ used suffix, LengthsWire slots space lengths final used ∧ Advance before after bits used suffix := by
  induction slots generalizing space final before after bits lengths with
  | zero =>
    unfold readLengths at read
    split at read
    · rename_i doneSpace
      subst space
      cases read
      exact ⟨[], bits, .complete 0, .refl rep count⟩
    · rename_i restSpace
      cases read
      exact ⟨[], bits, .exhausted (by omega), .refl rep count⟩
  | succ slots ih =>
    unfold readLengths at read
    split at read
    · rename_i doneSpace
      subst space
      cases read
      exact ⟨[], bits, .complete _, .refl rep count⟩
    · rename_i restSpace
      obtain ⟨⟨value, cursor⟩, lengthRead, next⟩ := bind_ok read
      simp only [] at next
      split at next
      · contradiction
      · rename_i fits
        obtain ⟨⟨tailLengths, tailSpace, tailCursor⟩, lengthsRead, done⟩ := bind_ok next
        cases done
        obtain ⟨middle, first⟩ := readLength_sound rep count lengthRead
        obtain ⟨body, suffix, wire, second⟩ := ih first.rep first.count lengthsRead
        exact ⟨value.bits ++ body, suffix, .next (by omega) (by omega) wire, first.trans second⟩

private theorem finish_sound {skip : Skip} {explicit : List Length} {space : Nat} {table : Table}
    (read : finish skip explicit space = .ok table) :
    table.lengths = orderedLengths skip explicit ∧
    match table.codes with
    | .singleton _ => 0 < space
    | .canonical _ => space = 0 := by
  simp only [finish] at read
  split at read
  · rename_i zero
    split at read
    · split at read <;> try contradiction
      cases read
      exact ⟨rfl, zero⟩
    · contradiction
  · rename_i positive
    split at read <;> try contradiction
    cases read
    exact ⟨rfl, by omega⟩

private theorem prefix_bound {slots space final : Nat} {lengths : List Length} {bits : List Bool}
    (wire : LengthsWire slots space lengths final bits) : bits.length ≤ 4 * slots := by
  induction wire with
  | complete _ => simp
  | exhausted _ => simp
  | @next _ _ _ value _ _ _ _ _ ih =>
    have width : value.bits.length ≤ 4 := by cases value <;> decide
    simp only [List.length_append]
    omega

theorem LengthsWire.exhausts_slots {slots space final : Nat} {lengths : List Length} {bits : List Bool}
    (wire : LengthsWire slots space lengths final bits) (incomplete : 0 < final) :
    lengths.length = slots := by
  induction wire <;> simp_all

theorem read_sound {bitLimit : Nat} {before after : LSBReader} {input : List Bool} {table : Table}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read bitLimit before = .ok (table, after)) :
    ∃ used suffix, Wire used table ∧ input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit ∧ used.length ≤ 74 := by
  unfold Formats.Compression.Brotli.Huffman.CodeLengths.read at read
  obtain ⟨⟨selector, cursor⟩, headerRead, next⟩ := bind_ok read
  obtain ⟨skip, skipRead, next⟩ := bind_ok next
  obtain ⟨⟨explicit, space, endCursor⟩, bodyRead, next⟩ := bind_ok next
  obtain ⟨builtTable, finished, done⟩ := bind_ok next
  cases done
  have hskip := select_sound skipRead
  subst selector
  obtain ⟨_, middle, header⟩ := take_sound rep count headerRead
  obtain ⟨body, suffix, wire, advance⟩ := readLengths_sound header.rep header.count bodyRead
  have total := header.trans advance
  obtain ⟨lengths, kind⟩ := finish_sound finished
  refine ⟨_, suffix, ⟨skip, explicit, space, body, rfl, wire, lengths, kind⟩,
    total.split, total.rep, total.count, total.offset, ?_, ?_⟩
  · have budget := total.budget
    dsimp at budget
    omega
  · have bound := prefix_bound wire
    simp only [List.length_append, natBits_length]
    omega

theorem Table.singleton_code {table : Table} {only : Nat}
    (kind : table.codes = .singleton only) : only < 18 ∧ table.codeFor only = some (0, 0) ∧
      ∀ other, only ≠ other → table.codeFor other = none := by
  have one := table.checked
  rw [kind] at one
  have member : only ∈ activeSymbols table.lengths := by
    change activeSymbols table.lengths = [only] at one
    simp [one]
  have range := List.mem_range.mp ((List.mem_filter.mp member).1)
  exact ⟨range, by simp [Brotli.Huffman.CodeLengths.Table.codeFor, kind],
    fun other ne => by simp [Brotli.Huffman.CodeLengths.Table.codeFor, kind, ne]⟩

theorem Table.canonical_code {table : Table} {codes : HuffmanTable} {symbol : Nat}
    (kind : table.codes = .canonical codes) (index : symbol < table.lengths.length)
    (positive : 0 < table.lengths[symbol].value) :
    ∃ code width, table.codeFor symbol = some (code, width) ∧ 0 < width ∧ width ≤ 5 ∧
      code < 2 ^ width ∧ lookupEntry codes.entries code width = some symbol ∧
      ∀ depth < width, lookupEntry codes.entries (code >>> (width - depth)) depth = none := by
  have checked := table.checked
  rw [kind] at checked
  have get : symbol < (table.lengths.map Length.value).length := by simpa using index
  obtain ⟨code, width, encoded, valid⟩ :=
    Deflate.HuffmanTable.ofLengths_symOK checked.2 get (by simpa using positive)
  have maxWidth : codes.maxBits = 5 := by
    have built := checked.2
    simp only [HuffmanTable.ofLengths] at built
    split at built <;> cases built <;> rfl
  exact ⟨code, width, by simpa [Brotli.Huffman.CodeLengths.Table.codeFor, kind] using encoded,
    valid.pos, maxWidth ▸ valid.le, valid.lt, valid.found, valid.prefixFree⟩

end Silmaril.Proofs.Formats.Compression.Brotli.Huffman.CodeLengths
