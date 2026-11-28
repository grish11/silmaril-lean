module

public import Silmaril.Formats.Compression.Zstd.SequenceTables.Defs
import Silmaril.Formats.Compression.Zstd.FseTable.Thms
import Silmaril.Formats.Compression.Zstd.FseTable.NCount.Thms
import Silmaril.Formats.Compression.Zstd.LiteralBlock.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.SequenceTables

open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Compression.Zstd.SequenceTables

theorem resolveTable_sound {alphabet : FseTable.Alphabet} {mode : Nat}
    {input rest : List UInt8} {table : Table}
    (success : resolveTable alphabet mode input = .ok (table, rest)) :
    ∃ used, input = used ++ rest ∧ TableWire alphabet mode used rest table := by
  unfold resolveTable at success
  split at success
  · cases h : FseTable.selectPredefined (tableLimits alphabet) alphabet 0 input with
    | error reason => simp [h, Except.mapError, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨chosen, tail⟩ := pair
      simp only [h, Except.mapError, bind, Except.bind, pure, Except.pure] at success
      cases success
      obtain ⟨_, same, valid, wire, good⟩ := FseTable.selectPredefined_sound h
      exact ⟨[], same.symm, .predefined valid wire good⟩
  · cases input with
    | nil => cases success
    | cons byte tail =>
      by_cases valid : byte.toNat < (tableLimits alphabet).symbols
      · simp only [ite_eq_left valid] at success
        cases success
        exact ⟨[byte], rfl, .rle valid⟩
      · simp [valid] at success
  · cases h : FseTable.NCount.readTable (transmittedLimits alphabet) input with
    | error reason => simp [h, Except.mapError, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨parsed, chosen⟩ := pair
      simp only [h, Except.mapError, bind, Except.bind, pure, Except.pure] at success
      cases success
      obtain ⟨valid, wire, good⟩ := FseTable.NCount.readTable_sound h
      obtain ⟨used, _, _, partition, size, _⟩ := valid.1
      exact ⟨used, partition, .transmitted rfl size.symm (partition ▸ valid) wire good⟩
  · cases success

theorem resolveUsing_sound {ε : Type} {translate : Error → ε}
    {readTable : FseTable.Alphabet → Nat → List UInt8 → Except ε (Table × List UInt8)}
    {relation : TableRelation} {limits : Limits} {input : List UInt8} {result : Section}
    (table_sound : ∀ {alphabet mode input rest table},
      readTable alphabet mode input = .ok (table, rest) →
        ∃ used, input = used ++ rest ∧ relation alphabet mode used rest table)
    (success : resolveUsing translate readTable limits input = .ok result) :
    input.length ≤ limits.inputBytes ∧ result.count ≤ limits.sequences ∧
      SectionLayout relation input result := by
  unfold resolveUsing at success
  split at success
  · cases success
  rename_i inputFits
  have within : input.length ≤ limits.inputBytes :=
    List.drop_eq_nil_iff.mp (Classical.not_not.mp inputFits)
  cases h : LiteralBlock.readSequenceCount input with
  | error reason => simp [h, Except.mapError, bind, Except.bind] at success
  | ok pair =>
    obtain ⟨count, rest⟩ := pair
    obtain ⟨encoded, partition, countWire⟩ := LiteralBlock.readSequenceCount_sound h
    simp only [h, Except.mapError, bind, Except.bind] at success
    split at success
    · cases success
    rename_i countFits
    split at success
    · rename_i zero
      subst count
      cases rest with
      | nil =>
        cases success
        exact ⟨within, Nat.zero_le _, by simpa [partition] using SectionLayout.empty (relation := relation) countWire⟩
      | cons byte tail => cases success
    · rename_i nonzero
      cases rest with
      | nil => cases success
      | cons byte descriptions =>
        simp only at success
        split at success
        · cases success
        rename_i reserved
        cases hll : readTable .literalLength (literalMode byte) descriptions with
        | error reason => simp [hll] at success
        | ok ll =>
          obtain ⟨literalLength, afterLiteral⟩ := ll
          cases hof : readTable .offset (offsetMode byte) afterLiteral with
          | error reason => simp [hll, hof] at success
          | ok ofc =>
            obtain ⟨offset, afterOffset⟩ := ofc
            cases hml : readTable .matchLength (matchMode byte) afterOffset with
            | error reason => simp [hll, hof, hml] at success
            | ok ml =>
              obtain ⟨matchLength, stream⟩ := ml
              simp only [hll, hof, hml, pure, Except.pure] at success
              split at success
              · cases success
              · rename_i hasStream
                cases success
                obtain ⟨llBytes, llPartition, llWire⟩ := table_sound hll
                obtain ⟨ofBytes, ofPartition, ofWire⟩ := table_sound hof
                obtain ⟨mlBytes, mlPartition, mlWire⟩ := table_sound hml
                rw [mlPartition] at ofWire ofPartition
                rw [ofPartition] at llWire llPartition
                rw [partition, llPartition]
                refine ⟨?_, Nat.le_of_not_gt countFits, ?_⟩
                · simpa [partition, llPartition] using within
                · simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
                    (SectionLayout.coded (relation := relation) (tables := ⟨literalLength, offset, matchLength⟩)
                      countWire (Nat.pos_of_ne_zero nonzero) (Classical.not_not.mp reserved)
                      (by simpa only [List.append_assoc] using llWire) ofWire mlWire (by simpa using hasStream))

theorem resolve_sound {limits : Limits} {input : List UInt8} {result : Section}
    (success : resolve limits input = .ok result) :
    input.length ≤ limits.inputBytes ∧ result.count ≤ limits.sequences ∧ SectionWire input result := by
  obtain ⟨inputFits, countFits, layout⟩ := resolveUsing_sound (translate := id) (readTable := resolveTable)
    (relation := TableWire) (fun h => resolveTable_sound h) success
  refine ⟨inputFits, countFits, ?_⟩
  cases layout with
  | empty count => exact .empty count
  | coded count positive reserved ll ofc ml stream => exact .coded count positive reserved ll ofc ml stream

private theorem boundedRow {limits : FseTable.Limits} {dist : FseTable.Distribution}
    {table : FseTable.Table} {state extra : Nat} {row : FseTable.Row}
    (valid : dist.Valid limits) (good : table.WellFormed dist)
    (lookup : table.rows[state]? = some row) (field : extra < 2 ^ row.bits) :
    table.log ≤ limits.accuracyLog ∧ state < 2 ^ table.log ∧ row.symbol < limits.symbols ∧
      row.bits ≤ table.log ∧ row.baseline + extra < 2 ^ table.log := by
  obtain ⟨stateFits, symbolFits, bitsFit, nextFits⟩ := FseTable.state_bounds good lookup field
  refine ⟨?_, stateFits, ?_, bitsFit, nextFits⟩
  · rw [good.1]
    exact Nat.le_trans valid.2.1 (Nat.min_le_left _ _)
  · exact Nat.lt_of_lt_of_le symbolFits (Nat.le_trans valid.2.2.1 (Nat.min_le_left _ _))

theorem fse_state_bounds {alphabet : FseTable.Alphabet} {mode state extra : Nat}
    {used rest : List UInt8} {table : FseTable.Table} {row : FseTable.Row}
    (wire : TableWire alphabet mode used rest (.fse table))
    (lookup : table.rows[state]? = some row) (field : extra < 2 ^ row.bits) :
    table.log ≤ (tableLimits alphabet).accuracyLog ∧ state < 2 ^ table.log ∧
      row.symbol < (tableLimits alphabet).symbols ∧ row.bits ≤ table.log ∧
      row.baseline + extra < 2 ^ table.log := by
  cases wire with
  | predefined valid _ good => exact boundedRow valid good lookup field
  | transmitted _ _ valid _ good => exact boundedRow valid.2.1 good lookup field

theorem suffix_exact {input : List UInt8} {result : Section} (wire : SectionWire input result) :
    input.drop (input.length - result.bitstream.length) = result.bitstream := by
  cases wire with
  | empty _ => simp [Section.bitstream]
  | @coded encoded ll ofc ml stream mode count tables _ _ _ _ _ _ _ =>
    let header := encoded ++ [mode] ++ ll ++ ofc ++ ml
    change (header ++ stream).drop ((header ++ stream).length - stream.length) = stream
    simp only [List.length_append, Nat.add_sub_cancel, List.drop_left]

end Silmaril.Proofs.Formats.Compression.Zstd.SequenceTables
