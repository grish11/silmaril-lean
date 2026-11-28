module

public import Silmaril.Formats.Compression.Zstd.FseTable.Defs

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.FseTable

open Silmaril.Formats.Compression.Zstd.FseTable

open Silmaril.Formats.Compression.Zstd.FseTable.Internal

private theorem validate_sound {limits : Limits} {dist : Distribution}
    (success : validate limits dist = .ok ()) : dist.Valid limits := by
  simp only [validate] at success
  split at success
  · cases success
  · rename_i logFits
    obtain ⟨above, below⟩ := not_or.mp logFits
    split at success
    · cases success
    · rename_i symbolFits
      split at success
      · cases success
      · rename_i checkedWeights
        have weights : ∀ weight ∈ dist.weights, -1 ≤ weight := by
          simpa using checkedWeights
        split at success
        · cases success
        · rename_i active
          split at success
          · cases success
          · rename_i mass
            exact ⟨Nat.le_of_not_gt above, Nat.le_of_not_gt below,
              Nat.le_of_not_gt symbolFits, weights, Nat.le_of_not_gt active,
              Decidable.not_not.mp mass⟩

private theorem assemble_sound {dist : Distribution} {table : Table}
    (success : assemble dist = .ok table) :
    TableWire dist table ∧ table.WellFormed dist := by
  let ordered := (placements dist).mergeSort fun left right => left.1 ≤ right.1
  let symbols := ordered.map Prod.snd
  let rows := symbols.mapIdx (rowFor dist symbols)
  simp only [assemble] at success
  split at success
  · cases success
  · rename_i indexing
    have order : ordered.map Prod.fst = List.range dist.size := Decidable.not_not.mp indexing
    have rowCount : rows.length = dist.size := by
      simpa only [rows, symbols, List.length_mapIdx, List.length_map, List.length_range]
        using congrArg List.length order
    split at success
    · cases success
    · rename_i checkedRows
      have checked : (rows.all fun row => decide (row.Valid dist)) = true := by
        simpa [rows, symbols, ordered] using checkedRows
      have rowsValid : ∀ row ∈ rows, row.Valid dist := by
        simpa using List.all_eq_true.mp checked
      split at success
      · cases success
      · rename_i checkedCounts
        cases success
        have counts : dist.weights.zipIdx.all
            (fun (weight, symbol) => (rows.map Row.symbol).count symbol == slots weight) =
            true := by
          simpa using checkedCounts
        refine ⟨⟨symbols, ⟨ordered, List.mergeSort_perm _ _, order, rfl⟩, rfl, rfl⟩,
          rfl, rowCount, rowsValid, ?_⟩
        intro symbol weight lookup
        have present : (weight, symbol) ∈ dist.weights.zipIdx := List.mem_zipIdx_iff_getElem?.mpr lookup
        exact beq_iff_eq.mp (List.all_eq_true.mp counts (weight, symbol) present)

theorem build_sound {limits : Limits} {dist : Distribution} {table : Table}
    (success : build limits dist = .ok table) :
    dist.Valid limits ∧ TableWire dist table ∧ table.WellFormed dist := by
  cases validated : validate limits dist with
  | error error => simp [build, validated, bind, Except.bind] at success
  | ok result =>
    cases result
    simp only [build, validated, bind, Except.bind] at success
    exact ⟨validate_sound validated, assemble_sound success⟩

theorem row_agrees {dist : Distribution} {table : Table} {state : Nat} {row : Row}
    (wire : TableWire dist table) (lookup : table.rows[state]? = some row) :
    ∃ symbols symbol, LayoutWire dist symbols ∧ symbols[state]? = some symbol ∧
      row = rowFor dist symbols state symbol := by
  obtain ⟨symbols, layout, _, shape⟩ := wire
  rw [shape, List.getElem?_mapIdx] at lookup
  cases found : symbols[state]? with
  | none => simp [found] at lookup
  | some symbol =>
    simp [found] at lookup
    exact ⟨symbols, symbol, layout, found, lookup.symm⟩

theorem state_bounds {dist : Distribution} {table : Table} {state extra : Nat} {row : Row}
    (wellFormed : table.WellFormed dist) (lookup : table.rows[state]? = some row)
    (field : extra < 2 ^ row.bits) :
    state < 2 ^ table.log ∧ row.symbol < dist.weights.length ∧ row.bits ≤ table.log ∧
      row.baseline + extra < 2 ^ table.log := by
  obtain ⟨log, size, valid, _⟩ := wellFormed
  obtain ⟨stateFits, _⟩ := List.getElem?_eq_some_iff.mp lookup
  obtain ⟨symbolFits, widthFits, baseFits⟩ := valid row (List.mem_of_getElem? lookup)
  rw [log]
  change state < dist.size ∧ row.symbol < dist.weights.length ∧ row.bits ≤ dist.log ∧
    row.baseline + extra < dist.size
  exact ⟨size ▸ stateFits, symbolFits, widthFits, by omega⟩

theorem table_size_le {limits : Limits} {dist : Distribution} {table : Table}
    (success : build limits dist = .ok table) : table.rows.length ≤ 2 ^ limits.logCap := by
  obtain ⟨valid, _, formed⟩ := build_sound success
  rw [formed.2.1]
  exact Nat.pow_le_pow_right (by decide) valid.2.1

theorem selectPredefined_sound {limits : Limits} {alphabet : Alphabet} {mode : UInt8}
    {input rest : List UInt8} {table : Table}
    (success : selectPredefined limits alphabet mode input = .ok (table, rest)) :
    mode = 0 ∧ rest = input ∧ (predefined alphabet).Valid limits ∧
      TableWire (predefined alphabet) table ∧ table.WellFormed (predefined alphabet) := by
  unfold selectPredefined at success
  split at success
  · rename_i zero
    cases built : build limits (predefined alphabet) with
    | error err => simp [built, Except.map] at success
    | ok result =>
      simp [built, Except.map] at success
      obtain ⟨rfl, rfl⟩ := success
      exact ⟨zero, rfl, build_sound built⟩
  · cases success

end Silmaril.Proofs.Formats.Compression.Zstd.FseTable
