module

public import Silmaril.Formats.Compression.Brotli.Huffman.MainTable.Defs
import Silmaril.Formats.Compression.Brotli.Huffman.MainLengths.Thms
import Silmaril.Formats.Compression.Deflate.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Huffman.MainTable

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.Huffman
open Silmaril.Formats.Compression.Brotli.Huffman.MainTable

private theorem kraft_eq {lengths : List Nat} (bound : ∀ depth ∈ lengths, depth ≤ 15) :
    kraftSum lengths 15 = MainLengths.kraft lengths := by
  change lengths.foldl _ 0 = MainLengths.kraft lengths
  rw [Deflate.kraft_foldl, Nat.zero_add]
  unfold kraftTotal MainLengths.kraft
  congr 1
  apply List.map_congr_left
  intro depth mem
  unfold MainLengths.mass
  split
  · rfl
  · congr 1
    change 2 ^ (15 - depth) = (2 ^ 15) >>> depth
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_div (bound depth mem) (by decide)]

private theorem checked_codes {lengths : List Nat}
    (bound : ∀ depth ∈ lengths, depth ≤ 15) (mass : MainLengths.kraft lengths = 32768) :
    isCompleteCode lengths 15 = true ∧ isValidLengths lengths 15 = true := by
  have every : (lengths.all fun depth => decide (depth ≤ 15)) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using bound
  simp [isCompleteCode, isValidLengths, every, kraft_eq bound, mass, Nat.shiftLeft_eq]

private theorem bind_ok {α β : Type} {action : Except Error α} {next : α → Except Error β}
    {answer : β} (read : (action >>= next) = .ok answer) :
    ∃ result, action = .ok result ∧ next result = .ok answer := by
  cases action with
  | error _ => cases read
  | ok value => exact ⟨value, rfl, read⟩

private theorem map_ok {α : Type} {action : Except MainLengths.Error α} {out : α}
    (read : action.mapError Error.lengths = .ok out) : action = .ok out := by
  cases action <;> cases read <;> rfl

private theorem install_lengths {lengths : List Nat} {table : Table}
    (read : Internal.install lengths = .ok table) : table.lengths = lengths := by
  unfold Internal.install at read
  split at read <;> cases read <;> rfl

private theorem dimensions (table : Table) :
    table.decoder.alphabetSize = table.lengths.length ∧ table.decoder.maxBits = 15 := by
  have built := table.installed
  simp only [HuffmanTable.ofLengths] at built
  split at built
  · contradiction
  · injection built with shape
    rw [← shape]
    exact ⟨rfl, rfl⟩

theorem read_sound {limits : MainLengths.Limits} {alphabet : Nat}
    {secondary : Brotli.Huffman.CodeLengths.Table} {before after : LSBReader}
    {input : List Bool} {table : Table} (rep : before.Rep input) (count : before.count < 8)
    (read : read limits alphabet secondary before = .ok (table, after)) :
    MainLengths.read limits alphabet secondary before = .ok (table.lengths, after) ∧
    table.lengths.length = alphabet ∧ table.decoder.alphabetSize = alphabet ∧ table.decoder.maxBits = 15 ∧
    isCompleteCode table.lengths 15 = true ∧ 0 < alphabet ∧ alphabet ≤ 704 ∧ alphabet ≤ limits.alphabet ∧
    ∃ used suffix, MainLengths.RunsWire secondary MainLengths.History.start alphabet 32768 used table.lengths ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ limits.bits := by
  unfold Formats.Compression.Brotli.Huffman.MainTable.read at read
  obtain ⟨⟨lengths, cursor⟩, expanded, next⟩ := bind_ok read
  obtain ⟨built, installed, done⟩ := bind_ok next
  cases done
  have lengthsMatch := install_lengths installed
  rw [← lengthsMatch] at expanded
  have expansion := map_ok expanded
  obtain ⟨positive, standard, caller, used, suffix, wire, exactBits, rest, alignment, offset, bitBound⟩ :=
    MainLengths.read_sound rep count expansion
  obtain ⟨size, mass, depths, _⟩ := MainLengths.RunsWire.bounds wire
  obtain ⟨symbols, width⟩ := dimensions table
  exact ⟨expansion, size, symbols.trans size, width, (checked_codes depths mass).1,
    positive, standard, caller, used, suffix, wire, exactBits, rest, alignment, offset, bitBound⟩

theorem read_after_lengths {limits : MainLengths.Limits} {alphabet : Nat}
    {secondary : Brotli.Huffman.CodeLengths.Table} {before after : LSBReader} {input : List Bool}
    {lengths : List Nat} (rep : before.Rep input) (count : before.count < 8)
    (expanded : MainLengths.read limits alphabet secondary before = .ok (lengths, after)) :
    ∃ table, read limits alphabet secondary before = .ok (table, after) ∧ table.lengths = lengths := by
  obtain ⟨_, _, _, _, _, wire, _⟩ := MainLengths.read_sound rep count expanded
  obtain ⟨_, mass, depths, _⟩ := MainLengths.RunsWire.bounds wire
  have valid := (checked_codes depths mass).2
  cases installed : HuffmanTable.ofLengths lengths 15 with
  | none => simp [HuffmanTable.ofLengths, valid] at installed
  | some decoder =>
    have installedTable : Internal.install lengths = .ok ⟨lengths, decoder, installed⟩ := by
      unfold Internal.install
      split
      · rename_i missing
        rw [installed] at missing
        contradiction
      · rename_i native assigned
        have same : native = decoder := Option.some.inj (assigned.symm.trans installed)
        subst native
        rfl
    exact ⟨⟨lengths, decoder, installed⟩,
      by simp [Brotli.Huffman.MainTable.read, expanded, installedTable, Except.mapError, bind, Except.bind,
        pure, Except.pure], rfl⟩

theorem Table.ordinal (table : Table) (ordinal : Nat) :
    let expected := table.lengths[ordinal]?.map fun depth =>
      ({ symbol := ordinal, length := depth,
         code := if depth = 0 then 0 else
           (nextCode (countByLength table.lengths 15)).getD (depth - 1) 0 +
             (table.lengths.take ordinal).count depth } : CodeEntry)
    table.decoder.entries[ordinal]? = expected ∧
      table.decoder.encodeSymbol ordinal = expected.bind
        (fun entry => if entry.length = 0 then none else some (entry.code, entry.length)) := by
  obtain ⟨lengths, decoder, installed⟩ := table
  unfold HuffmanTable.ofLengths at installed
  split at installed
  · contradiction
  · rename_i good
    have valid : isValidLengths lengths 15 = true := by simpa using good
    simp only [Option.some.injEq] at installed
    subst decoder
    let expected := lengths[ordinal]?.map fun depth =>
      ({ symbol := ordinal, length := depth,
         code := if depth = 0 then 0 else
           (nextCode (countByLength lengths 15)).getD (depth - 1) 0 +
             (lengths.take ordinal).count depth } : CodeEntry)
    have atOrdinal : (assignCodes lengths 15)[ordinal]? = expected := by
      rw [Deflate.assignCodes_getElem?]
      cases h : lengths[ordinal]? with
      | none => simp [expected, h]
      | some depth =>
        have fits := Deflate.isValidLengths_le lengths 15 valid depth (List.mem_of_getElem? h)
        by_cases zero : depth = 0
        · simp [expected, h, canonEntry, zero]
        · simp [expected, h, canonEntry, zero, Nat.not_lt_of_ge fits]
    refine ⟨atOrdinal, ?_⟩
    change _ = expected.bind (fun entry => if entry.length = 0 then none else some (entry.code, entry.length))
    simp only [HuffmanTable.encodeSymbol, Deflate.listGet_eq, List.getElem?_map, atOrdinal]
    cases expected with
    | none => rfl
    | some entry =>
      by_cases zero : entry.length = 0
      · simp [zero]
      · have positive : 0 < entry.length := by omega
        simp [zero, positive]

end Silmaril.Proofs.Formats.Compression.Brotli.Huffman.MainTable
