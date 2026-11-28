module

public import Silmaril.Formats.Relational.NamedTable.Defs
import Silmaril.Proofs.Formats.Relational.NamedTable
import Silmaril.Semantics.Relational.Database.Thms
import Silmaril.Formats.Parquet.Reader.Thms

/-! Exact named insertion, preservation, and typed format round trips. -/

public section

namespace Silmaril.Formats.Relational.NamedTable

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet

variable {Name Id Kind Error Group : Type*} {Value : Kind → Type*}

@[simp] theorem schemaMatches_eq_true_iff [DecidableEq Id] [DecidableEq Kind]
    (expected actual : Scan.Schema Id Kind) : schemaMatches expected actual = true ↔ expected = actual :=
  Proofs.Formats.Relational.NamedTable.schemaMatches_eq_true_iff expected actual

/-- A collected EOS observation inserts exactly at the vacant name and
only under the exact expected ordered schema. -/
theorem importCollected_ok_iff [DecidableEq Name] [DecidableEq Id] [DecidableEq Kind]
    (db next : Packed Name Id Value) (name : Name) (expected : Scan.Schema Id Kind)
    (collected : Except Error (Events.Observation Id Value Error)) :
    importCollected db name expected collected = .ok next ↔
      db name = none ∧ ∃ rows : Scan.Table expected Value,
        collected = .ok ⟨⟨expected, rows⟩, .eos⟩ ∧
        next = Function.update db name (some ⟨expected, rows⟩) :=
  Proofs.Formats.Relational.NamedTable.importCollected_ok_iff db next name expected collected

/-- Successful import requires a vacant name and exact schema at EOS, and
returns the database with only that name updated. -/
theorem importArrow_ok_iff [DecidableEq Name] [DecidableEq Id] [DecidableEq Kind]
    (db next : Packed Name Id Value) (name : Name) (expected : Scan.Schema Id Kind)
    (stream : Events.EventStream Id Value Error) :
    importArrow db name expected stream = .ok next ↔
      db name = none ∧ ∃ rows : Scan.Table expected Value,
        stream.collect = .ok ⟨⟨expected, rows⟩, .eos⟩ ∧
        next = Function.update db name (some ⟨expected, rows⟩) :=
  importCollected_ok_iff db next name expected stream.collect

theorem importArrow_observe [DecidableEq Name] [DecidableEq Id] [DecidableEq Kind]
    {db next : Packed Name Id Value} {name : Name} {expected : Scan.Schema Id Kind}
    {stream : Events.EventStream Id Value Error} (ok : importArrow db name expected stream = .ok next) :
    ∃ rows : Scan.Table expected Value, stream.collect = .ok ⟨⟨expected, rows⟩, .eos⟩ ∧
      Scan.observePacked next name = some ⟨expected, rows⟩ := by
  obtain ⟨_, rows, collected, rfl⟩ := (importArrow_ok_iff db next name expected stream).mp ok
  exact ⟨rows, collected, by simp [Scan.observePacked, Database.Packed.erase, Database.Partial.map]⟩

theorem importArrow_preserves_other [DecidableEq Name] [DecidableEq Id] [DecidableEq Kind]
    {db next : Packed Name Id Value} {name other : Name} {expected : Scan.Schema Id Kind}
    {stream : Events.EventStream Id Value Error} (ok : importArrow db name expected stream = .ok next)
    (different : other ≠ name) : next other = db other := by
  obtain ⟨_, rows, _, rfl⟩ := (importArrow_ok_iff db next name expected stream).mp ok
  exact Function.update_of_ne different _ _

theorem importParquet_eq_denote [DecidableEq Name] [DecidableEq Id] [DecidableEq Kind]
    (db : Packed Name Id Value) (name : Name) (expected : Scan.Schema Id Kind)
    (opened : Reader.OpenResult Group Id Value Error) :
    importParquet db name expected opened = importCollected db name expected (Reader.denote opened) :=
  congrArg (importCollected db name expected) (Reader.collect_readAll opened)

theorem importArrowDependent_pack [DecidableEq Name] [DecidableEq Id] [DecidableEq Kind]
    (db : Dependent Name Id Value) (name : Name) (expected : Scan.Schema Id Kind)
    (stream : Events.EventStream Id Value Error) :
    (importArrowDependent db name expected stream).map Database.Dependent.pack =
      importArrow db.pack name expected stream := by
  unfold importArrowDependent
  cases importArrow db.pack name expected stream <;> simp [Except.map, Database.pack_unpack]

/-- Export observes exactly the original schema and ordered rows. -/
theorem exportArrow_collect (db : Packed Name Id Value) (name : Name) (sizes : List Nat)
    {table : Scan.Observation Id Value} (found : Scan.observePacked db name = some table)
    (count : sizes.sum = table.rowCount) :
    (exportArrow db name sizes).collect = .ok ⟨table, .eos⟩ :=
  Proofs.Formats.Relational.NamedTable.exportArrow_collect db name sizes found count

/-- The requested batch counts are exact, including at schema width zero. -/
theorem exportArrow_batchCounts (db : Packed Name Id Value) (name : Name) (sizes : List Nat)
    {table : Scan.Observation Id Value} (found : Scan.observePacked db name = some table)
    (count : sizes.sum = table.rowCount) :
    (exportArrow db name sizes).map (fun entry => entry.snd.batches.map AlignedColumns.rowCount) =
      .ok sizes :=
  Proofs.Formats.Relational.NamedTable.exportArrow_batchCounts db name sizes found count

theorem exportArrowDependent_collect (db : Dependent Name Id Value) (name : Name) (sizes : List Nat)
    {table : Scan.Observation Id Value} (found : Scan.observeDependent db name = some table)
    (count : sizes.sum = table.rowCount) :
    (exportArrowDependent db name sizes).collect = .ok ⟨table, .eos⟩ :=
  exportArrow_collect db.pack name sizes found count

/-- A Parquet typed source made from the same named export yields the same
event stream under full consumption. -/
theorem read_exportParquet (db : Packed Name Id Value) (name : Name) (sizes : List Nat) :
    (exportParquet db name sizes).bind (fun ⟨schema, source⟩ => Reader.readAll (.ok ⟨schema, source⟩)) =
      exportArrow db name sizes :=
  Proofs.Formats.Relational.NamedTable.read_exportParquet db name sizes

theorem import_exportArrow [DecidableEq Name] [DecidableEq Id] [DecidableEq Kind]
    (source target : Packed Name Id Value) (exportName dest : Name) (sizes : List Nat)
    {table : Scan.Observation Id Value} (found : Scan.observePacked source exportName = some table)
    (vacant : target dest = none) (count : sizes.sum = table.rowCount) :
    importArrow target dest table.schema (exportArrow source exportName sizes) =
      .ok (Function.update target dest (some ⟨table.schema, table.rows⟩)) := by
  unfold importArrow
  rw [exportArrow_collect source exportName sizes found count]
  simp [importCollected, vacant]

end Silmaril.Formats.Relational.NamedTable
