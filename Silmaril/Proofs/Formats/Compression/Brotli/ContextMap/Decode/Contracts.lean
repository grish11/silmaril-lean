module

public import Silmaril.Formats.Compression.Brotli.ContextMap.Decode.Defs
import Silmaril.Formats.Compression.Brotli.ContextMap.Thms
import Silmaril.Formats.Compression.Brotli.Huffman.Description.Thms
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.ContextMap.Decode

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.ContextMap (Kind)
open Silmaril.Formats.Compression.Brotli.ContextMap.Decode
open Silmaril.Formats.Compression.Brotli.ContextMap.Decode.Internal
open Silmaril.Formats.Compression.Brotli

private structure Advance (before after : Cursor) (input used suffix : List Bool) : Prop where
  split : input = used ++ suffix
  rep : after.reader.Rep suffix
  count : after.reader.count < 8
  offset : after.reader.totalRead = before.reader.totalRead + used.length
  budget : before.remaining = after.remaining + used.length

private theorem Advance.trans {before middle after : Cursor}
    {input a rest b suffix : List Bool}
    (first : Advance before middle input a rest) (second : Advance middle after rest b suffix) :
    Advance before after input (a ++ b) suffix := by
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
  | ok value => exact ⟨value, rfl, read⟩

private theorem mapError_ok {ε α : Type} {action : Except ε α} {f : ε → Error} {value : α}
    (read : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases read <;> rfl

private theorem take_sound {width value : Nat} {before after : Cursor} {input : List Bool}
    (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : take before width = .ok (value, after)) :
    value < 2 ^ width ∧ ∃ suffix, Advance before after input (natBits value width) suffix := by
  unfold take at read
  split at read <;> try contradiction
  rename_i cap
  split at read <;> try contradiction
  rename_i n cursor actual
  cases read
  obtain ⟨suffix, split, rep', fits, offset, count'⟩ := LSBReader.readBits_sound rep count actual
  refine ⟨fits, suffix, split, rep', count' ▸ Nat.mod_lt _ (by decide), ?_, ?_⟩
  · simpa only [natBits_length] using offset
  · simp only [natBits_length]
    omega

private theorem code_sound {before : Cursor} {after : LSBReader} {table : Huffman.Description.Table}
    {input : List Bool} {symbol : Nat} (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : table.readBounded before.remaining before.reader = .ok (symbol, after)) :
    ∃ code width suffix, table.codeFor symbol = some (code, width) ∧ width ≤ 15 ∧
      Advance before (before.advance after) input (msbBits code width) suffix := by
  obtain ⟨code, width, suffix, assigned, bounded, cap, split, rep', count', offset⟩ :=
    Huffman.Description.Table.readBounded_sound rep count read
  exact ⟨code, width, suffix, assigned, bounded, split, rep', count',
    by simpa [Cursor.advance, msbBits_length] using offset,
    by simp [Cursor.advance, offset, msbBits_length]; omega⟩

private theorem run_sound {trees rleMax value size : Nat} {table : Huffman.Description.Table}
    {before after : Cursor} {input : List Bool}
    (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : readRun trees rleMax table before = .ok (value, size, after)) :
    ∃ used suffix, RunWire trees rleMax table used value size ∧ Advance before after input used suffix := by
  unfold readRun at read
  obtain ⟨⟨symbol, cursor⟩, codeRead, next⟩ := bind_ok read
  simp only [] at next
  split at next <;> try contradiction
  rename_i validSymbol
  obtain ⟨⟨extra, final⟩, extraRead, done⟩ := bind_ok next
  cases done
  obtain ⟨code, width, rest, assigned, bounded, first⟩ := code_sound rep count (mapError_ok codeRead)
  obtain ⟨fits, suffix, second⟩ := take_sound first.rep first.count extraRead
  exact ⟨_, suffix, .emit (by omega) assigned bounded fits, first.trans second⟩

theorem RunWire.bounds {trees rleMax value count : Nat} {table : Huffman.Description.Table}
    {bits : List Bool} (wire : RunWire trees rleMax table bits value count) (treesPositive : 0 < trees) :
    value < trees ∧ 0 < count := by
  cases wire with
  | @emit symbol code width extra hs _ _ _ =>
    have positive := Nat.two_pow_pos (runWidth rleMax symbol)
    omega

theorem RunsWire.bounds {trees rleMax slots work : Nat} {table : Huffman.Description.Table}
    {bits : List Bool} {positions : List Nat}
    (wire : RunsWire trees rleMax table slots work bits positions) (treesPositive : 0 < trees) :
    positions.length = slots ∧ work ≤ slots ∧ ∀ index ∈ positions, index < trees := by
  induction wire with
  | done => simp
  | @step slots work value count _ _ tail slotsOk run _ ih =>
    obtain ⟨bound, positive⟩ := RunWire.bounds run treesPositive
    refine ⟨by simp [ih.1]; omega, by have := ih.2.1; omega, ?_⟩
    intro index member
    rcases List.mem_append.mp member with inRun | inTail
    · exact (List.eq_of_mem_replicate inRun) ▸ bound
    · exact ih.2.2 index inTail

private theorem expand_sound {trees rleMax fuel slots : Nat} {table : Huffman.Description.Table}
    {before after : Cursor} {input : List Bool} {positions : List Nat}
    (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : expand trees rleMax table fuel slots before = .ok (positions, after)) :
    ∃ work used suffix, work ≤ fuel ∧ RunsWire trees rleMax table slots work used positions ∧
      Advance before after input used suffix := by
  induction fuel generalizing slots before after input positions with
  | zero =>
    unfold expand at read
    split at read <;> try contradiction
    rename_i empty
    subst slots
    cases read
    exact ⟨0, [], input, Nat.zero_le _, .done, by exact ⟨rfl, rep, count, by simp, by simp⟩⟩
  | succ fuel ih =>
    unfold expand at read
    split at read
    · rename_i empty
      subst slots
      cases read
      exact ⟨0, [], input, Nat.zero_le _, .done, by exact ⟨rfl, rep, count, by simp, by simp⟩⟩
    · obtain ⟨⟨value, size, cursor⟩, runRead, next⟩ := bind_ok read
      simp only [] at next
      split at next <;> try contradiction
      rename_i fits
      obtain ⟨⟨tail, final⟩, tailRead, done⟩ := bind_ok next
      cases done
      obtain ⟨bits, rest, run, first⟩ := run_sound rep count runRead
      obtain ⟨work, tailBits, suffix, cap, runs, second⟩ := ih first.rep first.count tailRead
      exact ⟨work + 1, bits ++ tailBits, suffix, by omega, .step (by omega) run runs, first.trans second⟩

private theorem mtf_sound {order positions values : List Nat}
    (read : inverseMtf order positions = .ok values) : MtfWire order positions values := by
  induction positions generalizing order values with
  | nil =>
    cases read
    exact .done _
  | cons position positions ih =>
    unfold inverseMtf at read
    split at read <;> try contradiction
    rename_i value selected
    obtain ⟨tail, next, done⟩ := bind_ok read
    cases done
    exact .step selected (ih next)

private theorem mtf_bounds {order positions values : List Nat}
    (wire : MtfWire order positions values) :
    values.length = positions.length ∧ ∀ value ∈ values, value ∈ order := by
  induction wire with
  | done => simp
  | @step order positions values position value selected _ ih =>
    refine ⟨by simp [ih.1], ?_⟩
    intro v member
    rcases List.mem_cons.mp member with eq | inTail
    · exact eq ▸ List.mem_of_getElem? selected
    · rcases List.mem_cons.mp (ih.2 v inTail) with eq | present
      · exact eq ▸ List.mem_of_getElem? selected
      · exact List.mem_of_mem_eraseIdx present

private theorem mtf_append {order positions values : List Nat}
    (wire : MtfWire order positions values) (suffix : List Nat) :
    MtfWire (order ++ suffix) positions values := by
  induction wire with
  | done => exact .done _
  | @step order positions values position value selected _ ih =>
    have bound := (List.getElem?_eq_some_iff.mp selected).1
    apply MtfWire.step ((List.getElem?_append_left bound).trans selected)
    simpa only [List.eraseIdx_append_of_lt_length bound, List.cons_append] using ih

theorem MtfWire.fullTable {trees : Nat} {positions values : List Nat}
    (wire : MtfWire (List.range trees) positions values) (bound : trees ≤ 256) :
    MtfWire (List.range 256) positions values := by
  have size : trees + (256 - trees) = 256 := by omega
  rw [← size, List.range_add]
  exact mtf_append wire _

private theorem finish_sound {trees : Nat} {flag : Bool} {positions : List Nat} {result : Map}
    (read : finish trees flag positions = .ok result) :
    ∃ values, result = .coded trees values ∧ TransformWire trees flag positions values ∧
      ∀ index, index < trees → index ∈ values := by
  unfold finish at read
  obtain ⟨values, valuesRead, done⟩ := bind_ok read
  split at done <;> try contradiction
  rename_i all
  cases done
  refine ⟨values, rfl, ?_, fun index bound => ?_⟩
  · unfold transform at valuesRead
    cases flag
    · cases valuesRead
      exact .identity _
    · exact .inverse (mtf_sound valuesRead)
  · simpa using List.all_eq_true.mp all index (List.mem_range.mpr bound)

private theorem coded_sound {entries trees rleMax symbols : Nat} {table : Huffman.Description.Table}
    {before : Cursor} {after : LSBReader} {input : List Bool} {result : Map}
    (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : readCoded entries trees rleMax table symbols before = .ok (result, after)) :
    ∃ work body flag suffix values positions final, work ≤ symbols ∧ result = .coded trees values ∧
      after = final.reader ∧ RunsWire trees rleMax table entries work body positions ∧
      TransformWire trees flag positions values ∧ (∀ index, index < trees → index ∈ values) ∧
      Advance before final input (body ++ [flag]) suffix := by
  unfold readCoded at read
  obtain ⟨⟨positions, next⟩, expanded, read⟩ := bind_ok read
  obtain ⟨⟨flag, final⟩, flagRead, read⟩ := bind_ok read
  obtain ⟨found, finished, done⟩ := bind_ok read
  cases done
  obtain ⟨work, body, rest, cap, runs, first⟩ := expand_sound rep count expanded
  obtain ⟨flagBound, suffix, second⟩ := take_sound first.rep first.count flagRead
  obtain ⟨values, actual, transformed, used⟩ := finish_sound finished
  have bit : natBits flag 1 = [decide (flag ≠ 0)] := by
    have alternatives : flag = 0 ∨ flag = 1 := by omega
    rcases alternatives with rfl | rfl <;> decide
  exact ⟨work, body, _, suffix, values, positions, final,
    Nat.le_trans cap (Nat.min_le_right ..), actual, rfl, runs, transformed, used, bit ▸ first.trans second⟩

theorem read_sound {kind : Kind} {types : Nat} {limits : Limits} {before after : LSBReader}
    {input : List Bool} {result : Map} (rep : before.Rep input) (count : before.count < 8)
    (read : Silmaril.Formats.Compression.Brotli.ContextMap.Decode.read kind types limits before = .ok (result, after)) :
    1 ≤ types ∧ types ≤ 256 ∧ kind.extent types ≤ limits.entries ∧
    ∃ work used suffix, work ≤ limits.symbols ∧ Wire (kind.extent types) work used result ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ limits.bits := by
  unfold Silmaril.Formats.Compression.Brotli.ContextMap.Decode.read at read
  obtain ⟨⟨header, cursor⟩, prefixed, done⟩ := bind_ok read
  obtain ⟨lo, hi, entriesCap, used, rest, wire, split, rep', count', offset, bitCap⟩ :=
    ContextMap.read_sound rep count (mapError_ok prefixed)
  refine ⟨lo, hi, entriesCap, ?_⟩
  cases header with
  | implicit entries =>
    cases done
    cases wire
    have positive : 0 < kind.extent types := Nat.mul_pos (by cases kind <;> decide) (by omega)
    exact ⟨0, _, rest, Nat.zero_le _, .implicit positive, split, rep', count', offset, bitCap⟩
  | coded entries trees rleMax table =>
    cases wire with
    | @coded _ _ _ a b c multi extent countWire rleWire tableWire alphabet =>
      have first : Advance ⟨before, limits.bits⟩ ((⟨before, limits.bits⟩ : Cursor).advance cursor)
          input (a ++ b ++ c) rest :=
        ⟨split, rep', count', offset, by dsimp at bitCap; simp only [Cursor.advance, offset]; omega⟩
      obtain ⟨work, body, flag, suffix, values, positions, final, cap, rfl, rfl,
          runs, transform, coverage, next⟩ := coded_sound first.rep first.count done
      have total := first.trans next
      rw [← List.append_assoc] at total
      have budget := total.budget
      dsimp at budget
      exact ⟨work, _, suffix, cap, .coded (.coded multi extent countWire rleWire tableWire alphabet)
        runs transform coverage, total.split, total.rep, total.count, total.offset, by omega⟩

private theorem transform_bounds {trees slots : Nat} {flag : Bool} {positions values : List Nat}
    (wire : TransformWire trees flag positions values) (size : positions.length = slots)
    (bounds : ∀ index ∈ positions, index < trees) :
    values.length = slots ∧ ∀ index ∈ values, index < trees := by
  cases wire with
  | identity => exact ⟨size, bounds⟩
  | inverse mtf =>
    obtain ⟨length, within⟩ := mtf_bounds mtf
    exact ⟨length.trans size, fun index member => List.mem_range.mp (within index member)⟩

theorem Wire.valid {entries work : Nat} {bits : List Bool} {result : Map}
    (wire : Wire entries work bits result) :
    result.indices.length = entries ∧ work ≤ entries ∧ 1 ≤ result.treeCount ∧
      result.treeCount ≤ 256 ∧ (∀ index, index ∈ result.indices ↔ index < result.treeCount) := by
  cases wire with
  | implicit positive =>
    simp [Map.indices, Map.treeCount, List.mem_replicate, Nat.lt_one_iff, Nat.ne_of_gt positive]
  | coded header runs transform coverage =>
    obtain ⟨minTrees, maxTrees, _⟩ := ContextMap.Wire.coded_bounds header
    obtain ⟨size, cap, bounds⟩ := RunsWire.bounds runs (by omega)
    obtain ⟨length, range⟩ := transform_bounds transform size bounds
    exact ⟨length, cap, by simp [Map.treeCount]; omega, maxTrees,
      fun index => ⟨range index, coverage index⟩⟩

end Silmaril.Proofs.Formats.Compression.Brotli.ContextMap.Decode
