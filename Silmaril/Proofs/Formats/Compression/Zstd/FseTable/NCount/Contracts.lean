module

public import Silmaril.Formats.Compression.Zstd.FseTable.NCount.Defs
import Silmaril.Formats.Compression.Zstd.FseTable.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.FseTable.NCount

open Silmaril.Formats.Compression (LSBReader)
open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Compression.Zstd.FseTable
open Silmaril.Formats.Compression.Zstd.FseTable.NCount
open Silmaril.Formats.Compression.Zstd.FseTable.NCount.Internal

private def Advance (first last : LSBReader) : Prop :=
  (∃ used : List UInt8, first.input = used ++ last.input ∧
    last.totalRead + last.count = first.totalRead + first.count + 8 * used.length) ∧ last.count < 8

private theorem advance_refl {cursor : LSBReader} (count : cursor.count < 8) :
    Advance cursor cursor := ⟨⟨[], rfl, by simp⟩, count⟩

private theorem advance_trans {first middle last : LSBReader}
    (before : Advance first middle) (after : Advance middle last) : Advance first last := by
  obtain ⟨⟨prefixBytes, prefixShape, prefixBits⟩, _⟩ := before
  obtain ⟨⟨tailBytes, tailShape, tailBits⟩, count⟩ := after
  refine ⟨⟨prefixBytes ++ tailBytes, by simp [prefixShape, tailShape, List.append_assoc], ?_⟩, count⟩
  simp only [List.length_append]
  omega

private theorem readBit_advance {first last : LSBReader} {bit : Bool} (count : first.count < 8)
    (success : first.readBit = some (bit, last)) :
    last.totalRead = first.totalRead + 1 ∧ Advance first last := by
  obtain ⟨buffer, bits, input, read⟩ := first
  by_cases empty : bits = 0
  · subst bits
    cases input with
    | nil => cases success
    | cons byte tail =>
      cases success
      exact ⟨rfl, ⟨⟨[byte], rfl, by simp [LSBReader.refill]⟩, by simp [LSBReader.refill]⟩⟩
  · simp only [LSBReader.readBit, empty, ite_false] at success
    cases success
    change bits < 8 at count
    exact ⟨rfl, ⟨⟨[], rfl, by simp; omega⟩, by simp; omega⟩⟩

private theorem readBits_advance {first last : LSBReader} {bits value : Nat} (count : first.count < 8)
    (success : first.readBits bits = some (value, last)) :
    value < 2 ^ bits ∧ last.totalRead = first.totalRead + bits ∧ Advance first last := by
  induction bits generalizing first last value with
  | zero =>
    cases success
    exact ⟨by decide, by simp, advance_refl count⟩
  | succ bits ih =>
    cases head : first.readBit with
    | none => simp [LSBReader.readBits, head] at success
    | some pair =>
      obtain ⟨bit, middle⟩ := pair
      cases tail : middle.readBits bits with
      | none => simp [LSBReader.readBits, head, tail] at success
      | some pair =>
        obtain ⟨decoded, next⟩ := pair
        simp only [LSBReader.readBits, head, tail] at success
        cases success
        obtain ⟨firstWidth, advanced⟩ := readBit_advance count head
        obtain ⟨fieldBound, restWidth, finished⟩ := ih advanced.2 tail
        exact ⟨by cases bit <;> simp [Nat.pow_succ] <;> omega, by omega,
          advance_trans advanced finished⟩

private theorem readField_sound {cap bits value : Nat} {first last : LSBReader}
    (count : first.count < 8) (success : readField cap first bits = .ok (value, last)) :
    first.readBits bits = some (value, last) ∧ value < 2 ^ bits ∧
      Advance first last ∧ last.totalRead ≤ 8 * cap := by
  unfold readField at success
  split at success
  · cases success
  · rename_i budget
    cases got : first.readBits bits with
    | none => simp [got] at success
    | some pair =>
      obtain ⟨decoded, next⟩ := pair
      simp only [got] at success
      cases success
      obtain ⟨bound, size, advanced⟩ := readBits_advance count got
      exact ⟨rfl, bound, advanced, by omega⟩

private theorem readWeight_sound {cap remaining : Nat} {first last : LSBReader} {weight : Int}
    (count : first.count < 8) (success : readWeight cap remaining first = .ok (weight, last)) :
    WeightWire remaining first weight last ∧ Advance first last ∧ last.totalRead ≤ 8 * cap := by
  cases got : readField cap first (width remaining) with
  | error err => simp [readWeight, got, bind, Except.bind] at success
  | ok pair =>
    obtain ⟨low, middle⟩ := pair
    obtain ⟨firstField, _, advanced, within⟩ := readField_sound count got
    simp only [readWeight, got, bind, Except.bind] at success
    split at success
    · rename_i short
      cases success
      exact ⟨.short firstField short, advanced, within⟩
    · rename_i long
      cases extra : readField cap middle 1 with
      | error err => simp [extra] at success
      | ok pair =>
        obtain ⟨high, next⟩ := pair
        simp only [extra, pure, Except.pure] at success
        cases success
        obtain ⟨extraField, _, finished, budget⟩ := readField_sound advanced.2 extra
        exact ⟨.long firstField (Nat.le_of_not_gt long) extraField, advance_trans advanced finished, budget⟩

private theorem readZeros_sound {cap fuel available count : Nat} {first last : LSBReader}
    (short : first.count < 8) (success : readZeros cap fuel available first = .ok (count, last)) :
    ZeroRunWire first count last ∧ count ≤ available ∧ Advance first last ∧ last.totalRead ≤ 8 * cap := by
  induction fuel generalizing available first last count with
  | zero => cases success
  | succ fuel ih =>
    cases got : readField cap first 2 with
    | error err => simp [readZeros, got, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨group, middle⟩ := pair
      obtain ⟨field, bound, advanced, within⟩ := readField_sound short got
      simp only [readZeros, got, bind, Except.bind] at success
      split at success
      · simp [throw] at success
      · rename_i budget
        split at success
        · rename_i more
          subst group
          cases reading : readZeros cap fuel (available - 3) middle with
          | error err => simp [reading] at success
          | ok pair =>
            obtain ⟨decoded, next⟩ := pair
            simp only [reading, pure, Except.pure] at success
            cases success
            obtain ⟨wire, length, finished, capFits⟩ := ih advanced.2 reading
            exact ⟨.more field wire, by omega, advance_trans advanced finished, capFits⟩
        · rename_i done
          cases success
          exact ⟨.stop field (by omega), by omega, advanced, within⟩

private theorem readCounts_sound {cap fuel available remaining : Nat} {first last : LSBReader}
    {weights : List Int} (short : first.count < 8) (beforeBudget : first.totalRead ≤ 8 * cap)
    (success : readCounts cap fuel available remaining first = .ok (weights, last)) :
    CountsWire remaining first weights last ∧ weights.length ≤ available ∧
      Advance first last ∧ last.totalRead ≤ 8 * cap := by
  induction fuel generalizing available remaining first weights last with
  | zero =>
    cases remaining with
    | zero => cases success; exact ⟨.done first, by simp, advance_refl short, beforeBudget⟩
    | succ remaining => cases success
  | succ fuel ih =>
    cases remaining with
    | zero => cases success; exact ⟨.done first, by simp, advance_refl short, beforeBudget⟩
    | succ remaining =>
      cases available with
      | zero => cases success
      | succ available =>
        cases got : readWeight cap (remaining + 1) first with
        | error err => simp [readCounts, got, bind, Except.bind] at success
        | ok pair =>
          obtain ⟨weight, middle⟩ := pair
          obtain ⟨weightWire, advanced, within⟩ := readWeight_sound short got
          simp only [readCounts, got, bind, Except.bind] at success
          split at success
          · simp [throw] at success
          · rename_i massFits
            split at success
            · rename_i zero
              subst weight
              cases run : readZeros cap (available + 1) available middle with
              | error err => simp [run] at success
              | ok pair =>
                obtain ⟨zeros, afterRun⟩ := pair
                obtain ⟨zeroWire, zerosFit, runAdvance, runFits⟩ := readZeros_sound advanced.2 run
                cases tail : readCounts cap fuel (available - zeros) (remaining + 1) afterRun with
                | error err => simp [run, tail] at success
                | ok pair =>
                  obtain ⟨counts, next⟩ := pair
                  simp only [run, tail, pure, Except.pure] at success
                  cases success
                  obtain ⟨wire, length, after, budget⟩ := ih runAdvance.2 runFits tail
                  refine ⟨.zeros (Nat.zero_lt_succ _) weightWire zeroWire wire, ?_,
                    advance_trans (advance_trans advanced runAdvance) after, budget⟩
                  simp only [List.length_cons, List.length_append, List.length_replicate]
                  omega
            · rename_i nonzero
              cases tail : readCounts cap fuel available (remaining + 1 - slots weight) middle with
              | error err => simp [tail] at success
              | ok pair =>
                obtain ⟨counts, next⟩ := pair
                simp only [tail, pure, Except.pure] at success
                cases success
                obtain ⟨wire, length, after, budget⟩ := ih advanced.2 within tail
                exact ⟨.nonzero (Nat.zero_lt_succ _) weightWire nonzero
                  (Nat.le_of_not_gt massFits) wire, by simpa using length,
                  advance_trans advanced after, budget⟩

private theorem counts_mass {remaining : Nat} {first last : LSBReader} {weights : List Int}
    (wire : CountsWire remaining first weights last) :
    (weights.map slots).sum = remaining ∧ ∀ weight ∈ weights, -1 ≤ weight := by
  induction wire with
  | done => simp
  | nonzero positive weightWire _ fits _ ih =>
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons, ih.1]
      omega
    · intro weight present
      rcases List.mem_cons.mp present with rfl | present
      · cases weightWire <;> simp [signedWeight] <;> omega
      · exact ih.2 weight present
  | zeros _ _ _ _ ih =>
    refine ⟨?_, ?_⟩
    · simp [slots, ih.1, List.sum_append, List.map_replicate]
    · intro weight present
      simp only [List.mem_cons, List.mem_append, List.mem_replicate] at present
      rcases present with rfl | ⟨_, rfl⟩ | present
      · decide
      · decide
      · exact ih.2 weight present

theorem read_sound {limits : NCount.Limits} {input : List UInt8} {result : Prefix}
    (success : NCount.read limits input = .ok result) : result.Valid limits input := by
  let first : LSBReader := ⟨0, 0, input, 0⟩
  cases accuracy : readField limits.byteCap first 4 with
  | error err => simp [NCount.read, first, accuracy, bind, Except.bind] at success
  | ok pair =>
    obtain ⟨low, afterLog⟩ := pair
    obtain ⟨field, _, opened, logInCap⟩ := readField_sound (by change 0 < 8; decide) accuracy
    have getLog : readField limits.byteCap ⟨0, 0, input, 0⟩ 4 = .ok (low, afterLog) := accuracy
    simp only [NCount.read, getLog, bind, Except.bind] at success
    split at success
    · simp [throw] at success
    · rename_i logFits
      cases parsed : readCounts limits.byteCap limits.table.symbolCap limits.table.symbolCap
          (2 ^ (low + 5)) afterLog with
      | error err => simp [parsed] at success
      | ok pair =>
        obtain ⟨weights, final⟩ := pair
        obtain ⟨countsWire, symbolFits, advanced, bitsFit⟩ := readCounts_sound opened.2 logInCap parsed
        obtain ⟨mass, weightsValid⟩ := counts_mass countsWire
        obtain ⟨⟨head, inputShape, extent⟩, padding⟩ := advance_trans opened advanced
        have boundary : head.length = (final.totalRead + 7) / 8 := by
          have initialRead : first.totalRead = 0 := rfl
          have initialCount : first.count = 0 := rfl
          rw [initialRead, initialCount] at extent
          omega
        simp only [parsed] at success
        split at success
        · simp [throw] at success
        · rename_i active
          split at success
          · simp [throw] at success
          · rename_i expected
            cases success
            have minLog : 5 ≤ low + 5 := by omega
            have byteFits : (final.totalRead + 7) / 8 ≤ limits.byteCap := by omega
            refine ⟨⟨head, afterLog, final, inputShape, boundary, rfl, ?_, countsWire, rfl, rfl⟩,
              ⟨minLog, Nat.le_of_not_gt logFits, symbolFits, weightsValid,
                Nat.le_of_not_gt active, mass⟩, byteFits, bitsFit, ?_⟩
            · simpa using field
            · intro count eq
              exact (show count = weights.length by simpa [eq] using expected).symm

theorem readTable_sound {limits : NCount.Limits} {input : List UInt8} {result : Prefix} {table : Table}
    (success : readTable limits input = .ok (result, table)) :
    result.Valid limits input ∧ TableWire result.distribution table ∧ table.WellFormed result.distribution := by
  cases parsed : NCount.read limits input with
  | error err => simp [readTable, parsed, bind, Except.bind] at success
  | ok found =>
    cases built : build limits.table found.distribution with
    | error err => simp [readTable, parsed, built, Except.mapError, bind, Except.bind] at success
    | ok constructed =>
      simp only [readTable, parsed, built, Except.mapError, bind, Except.bind, pure, Except.pure] at success
      cases success
      exact ⟨read_sound parsed, (FseTable.build_sound built).2⟩

end Silmaril.Proofs.Formats.Compression.Zstd.FseTable.NCount
