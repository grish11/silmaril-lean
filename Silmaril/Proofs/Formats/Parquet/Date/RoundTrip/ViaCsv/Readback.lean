module

public import Silmaril.Formats.Parquet.Date.RoundTrip.ViaCsv.Defs
public import Silmaril.Formats.Parquet.Date.RoundTrip.Defs
import Silmaril.Formats.Parquet.Date.ToCsv.Thms
import Silmaril.Formats.Parquet.Date.FromCsv.Thms
import Silmaril.Formats.Parquet.Date.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Date32.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.RoundTrip.ViaCsv

open Silmaril.Formats Parquet Date.RoundTrip Date.RoundTrip.ViaCsv

private theorem legs {limits : Limits} {name : String} {nullable : Bool} {input output : Bytes}
    (converted : convert limits name nullable input = .ok output) :
    ∃ csv, Date.ToCsv.convert limits.source limits.exportCsv name nullable input = .ok csv ∧
      Date.FromCsv.convert limits.importCsv limits.ipc limits.writer limits.readback name nullable csv =
        .ok output := by
  cases exported : Date.ToCsv.convert limits.source limits.exportCsv name nullable input with
  | error cause => simp [convert, exported, Except.mapError, Bind.bind, Except.bind] at converted
  | ok csv =>
    refine ⟨csv, rfl, ?_⟩
    cases imported : Date.FromCsv.convert limits.importCsv limits.ipc limits.writer limits.readback
        name nullable csv with
    | error cause => simp [convert, exported, imported, Except.mapError, Bind.bind, Except.bind] at converted
    | ok wire =>
      simpa [convert, exported, imported, Except.mapError, Bind.bind, Except.bind] using converted

private theorem binding_eq {limits : Date.Limits} {source : Bytes}
    {checked : Date.Checked} {group : Date.RowGroup}
    (opened : Date.openChecked limits source = .ok checked)
    (read : Date.readGroup limits source 0 = .ok group) :
    checked.binding = group.binding := by
  obtain ⟨snapshot, _, _, check, bound, _, _, _⟩ := (Date.readGroup_ok_iff _ _ _ _).mp read
  obtain ⟨checkedSnapshot, checkedBinding⟩ := (Date.openChecked_ok_iff _ _ _).mp opened
  cases Except.ok.inj (check.symm.trans checkedSnapshot)
  exact Except.ok.inj (checkedBinding.symm.trans bound)

theorem convert_readback {limits : Limits} {name : String} {nullable : Bool} {input output : Bytes}
    (converted : convert limits name nullable input = .ok output) :
    ∃ batches, ParquetObserves limits.source input ⟨name, nullable, batches⟩ ∧
      ParquetObserves limits.readback output ⟨name, nullable, [batches.flatten]⟩ := by
  obtain ⟨csv, exported, imported⟩ := legs converted
  obtain ⟨_, slots, readRows, _, encoded⟩ := Date.ToCsv.convert_eq_ok_iff.mp exported
  obtain ⟨batches, source, rfl⟩ := Date.ToCsv.readRows_eq_ok_iff.mp readRows
  obtain ⟨table, checked, group, decoded, opened, read, count, leaf, _, _, words⟩ :=
    Date.FromCsv.convert_readback imported
  have tableEq := Except.ok.inj (decoded.symm.trans (Csv.Typed.Codecs.Date32.decode_encode encoded))
  subst table
  have exactWords : group.date32Slots = batches.flatten := by
    simpa [Arrow.DateStream.FromCsv.slots, Arrow.DateStream.ToCsv.rows, List.map_map,
      Function.comp_def] using words
  have selected := (Date.Checked.readGroup_of_opened opened 0).trans read
  have descriptor : checked.binding.leaf = Date.FromIpc.leaf ⟨name, nullable, .day⟩ := by
    rw [binding_eq opened read, leaf]
  refine ⟨batches, source, checked, [group], opened, ?_, ?_⟩
  · simp [count, List.range_succ, List.mapM_cons, selected, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  · cases nullable <;> simp [descriptor, Date.FromIpc.leaf, exactWords]

theorem output_rows_eq_iff {limits : Limits} {name : String} {nullable : Bool}
    {left right leftOutput rightOutput : Bytes}
    (convertedLeft : convert limits name nullable left = .ok leftOutput)
    (convertedRight : convert limits name nullable right = .ok rightOutput) :
    Date.ToCsv.readRows limits.readback name nullable leftOutput =
      Date.ToCsv.readRows limits.readback name nullable rightOutput ↔
    Date.ToCsv.readRows limits.source name nullable left =
      Date.ToCsv.readRows limits.source name nullable right := by
  obtain ⟨leftBatches, leftSource, leftResult⟩ := convert_readback convertedLeft
  obtain ⟨rightBatches, rightSource, rightResult⟩ := convert_readback convertedRight
  rw [Date.ToCsv.readRows_eq_ok_iff.mpr ⟨_, leftSource, rfl⟩,
    Date.ToCsv.readRows_eq_ok_iff.mpr ⟨_, rightSource, rfl⟩,
    Date.ToCsv.readRows_eq_ok_iff.mpr ⟨_, leftResult, rfl⟩,
    Date.ToCsv.readRows_eq_ok_iff.mpr ⟨_, rightResult, rfl⟩]
  simp

end Silmaril.Proofs.Formats.Parquet.Date.RoundTrip.ViaCsv
