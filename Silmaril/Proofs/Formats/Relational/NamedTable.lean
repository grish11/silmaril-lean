module

public import Silmaril.Formats.Relational.NamedTable.Defs
import Silmaril.Formats.Parquet.Reader.Thms
import Mathlib.Data.List.OfFn

public section

namespace Silmaril.Proofs.Formats.Relational.NamedTable

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Relational.NamedTable

variable {Name Id Kind Error : Type*} {Value : Kind → Type*}

theorem schemaMatches_eq_true_iff [DecidableEq Id] [DecidableEq Kind]
    (expected actual : Scan.Schema Id Kind) : schemaMatches expected actual = true ↔ expected = actual := by
  rw [schemaMatches, decide_eq_true_eq]
  constructor
  · rcases expected with ⟨width, labels⟩
    rcases actual with ⟨width', labels'⟩
    intro equal
    have widths : width = width' := by simpa using congrArg List.length equal
    subst width'
    exact congrArg (PositionalSchema.mk width) (List.ofFn_injective equal)
  · rintro rfl
    rfl

theorem importCollected_ok_iff [DecidableEq Name] [DecidableEq Id] [DecidableEq Kind]
    (db next : Packed Name Id Value) (name : Name) (expected : Scan.Schema Id Kind)
    (collected : Except Error (Events.Observation Id Value Error)) :
    importCollected db name expected collected = .ok next ↔
      db name = none ∧ ∃ rows : Scan.Table expected Value,
        collected = .ok ⟨⟨expected, rows⟩, .eos⟩ ∧
        next = Function.update db name (some ⟨expected, rows⟩) := by
  cases found : db name with
  | some entry => simp [importCollected, found]
  | none =>
    rcases collected with error | ⟨⟨actual, rows⟩, status⟩
    · simp [importCollected, found]
    cases status with
    | eos =>
      by_cases same : expected = actual
      · subst actual
        simp only [importCollected, found, Option.isSome_none, Bool.false_eq_true, ite_false,
          schemaMatches_eq_true_iff, ite_true, Except.ok.injEq, true_and]
        constructor
        · intro saved
          exact ⟨rows, rfl, saved.symm⟩
        · rintro ⟨other, collected, saved⟩
          have sameRows : rows = other := eq_of_heq
            (Scan.Observation.mk.inj (congrArg Events.Observation.table collected)).2
          subst other
          exact saved.symm
      · simp [importCollected, found, schemaMatches_eq_true_iff, same, Ne.symm same]
    | closed => simp [importCollected, found]
    | readError _ => simp [importCollected, found]
    | closeError _ => simp [importCollected, found]

theorem exportArrow_collect (db : Packed Name Id Value) (name : Name) (sizes : List Nat)
    {table : Scan.Observation Id Value} (found : Scan.observePacked db name = some table)
    (count : sizes.sum = table.rowCount) :
    (exportArrow db name sizes).collect = .ok ⟨table, .eos⟩ := by
  have rows := List.flatten_splitLengths table.rows sizes count.ge
  simp [exportArrow, exportChunks, found, count, Except.map, Events.EventStream.collect,
    Events.Trace.collect, Events.Trace.rows, List.flatMap_map, Function.comp_def, rows]

theorem exportArrow_batchCounts (db : Packed Name Id Value) (name : Name) (sizes : List Nat)
    {table : Scan.Observation Id Value} (found : Scan.observePacked db name = some table)
    (count : sizes.sum = table.rowCount) :
    (exportArrow db name sizes).map (fun entry => entry.snd.batches.map AlignedColumns.rowCount) =
      .ok sizes := by
  have sizesExact := List.map_splitLengths_length table.rows sizes count.le
  simpa [exportArrow, exportChunks, found, count, Except.map, List.map_map, Function.comp_def,
    AlignedColumns.ofRows] using congrArg (Except.ok (ε := ExportError)) sizesExact

theorem read_exportParquet (db : Packed Name Id Value) (name : Name) (sizes : List Nat) :
    (exportParquet db name sizes).bind (fun ⟨schema, source⟩ => Reader.readAll (.ok ⟨schema, source⟩)) =
      exportArrow db name sizes := by
  have decoded {schema : Scan.Schema Id Kind} (chunks : List (Scan.Table schema Value)) :
      Reader.denoteGroups (Except.ok (ε := ExportError)) chunks = (chunks, .eos) := by
    induction chunks with
    | nil => rfl
    | cons chunk rest ih => simp [Reader.denoteGroups, ih]
  unfold exportParquet exportArrow
  rcases exportChunks db name sizes with error | ⟨schema, chunks⟩
  · rfl
  simp [Except.map, Except.bind, Reader.readAll_opened, decoded]

end Silmaril.Proofs.Formats.Relational.NamedTable
