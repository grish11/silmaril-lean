module

public import Silmaril.Formats.Parquet.Date.FromCsv.Defs
import Silmaril.Formats.Arrow.DateStream.FromCsv.Thms
import Silmaril.Formats.Parquet.Date.FromIpc.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.FromCsv

open Silmaril Silmaril.Formats
open Parquet Date.FromCsv

theorem convert_eq_ok_iff {csv : Arrow.DateStream.FromCsv.CsvLimits}
    {ipc : Arrow.ObservationLimits} {writer : FlatInt32Writer.Limits} {readback : Date.Limits}
    {name : String} {nullable : Bool} {input : Csv.Bytes} {output : Bytes} :
    convert csv ipc writer readback name nullable input = .ok output ↔
      ∃ intermediate, Arrow.DateStream.FromCsv.convert ipc csv name nullable input = .ok intermediate ∧
        Date.FromIpc.convert ipc.ipc writer readback intermediate = .ok output := by
  unfold convert
  cases Arrow.DateStream.FromCsv.convert ipc csv name nullable input with
  | error cause => simp [Except.mapError, Bind.bind, Except.bind]
  | ok intermediate =>
    cases written : Date.FromIpc.convert ipc.ipc writer readback intermediate <;>
      simp [written, Except.mapError, Bind.bind, Except.bind]

theorem convert_readback {csv : Arrow.DateStream.FromCsv.CsvLimits}
    {ipc : Arrow.ObservationLimits} {writer : FlatInt32Writer.Limits} {readback : Date.Limits}
    {name : String} {nullable : Bool} {input : Csv.Bytes} {output : Bytes}
    (written : convert csv ipc writer readback name nullable input = .ok output) :
    ∃ table checked group,
      Csv.Typed.Codecs.Date32.decode (Arrow.DateStream.FromCsv.schema name nullable) id input = .ok table ∧
      Date.openChecked readback output = .ok checked ∧ Date.readGroup readback output 0 = .ok group ∧
      checked.snapshot.groupCount = 1 ∧
      group.binding.leaf = Date.FromIpc.leaf ⟨name, nullable, .day⟩ ∧
      group.binding.annotation = .logicalAndConverted ∧
      group.rowCount = table.length ∧ group.date32Slots = Arrow.DateStream.FromCsv.slots table := by
  obtain ⟨intermediate, fromCsv, fromIpc⟩ := convert_eq_ok_iff.mp written
  obtain ⟨table, csvStream, decoded, csvRead, csvField, csvWords⟩ :=
    Arrow.DateStream.FromCsv.convert_readback fromCsv
  obtain ⟨ipcStream, dates, checked, group, ipcRead, _, batch, opened, read, agrees⟩ :=
    Date.FromIpc.convert_readback fromIpc
  have same := Except.ok.inj (ipcRead.symm.trans csvRead)
  subst ipcStream
  have days := Date.FromIpc.Matches.exactWords agrees
  rw [batch, List.map_cons, List.map_nil, List.cons.injEq] at csvWords
  obtain ⟨slots, _⟩ := csvWords
  have field : csvStream.field = ⟨name, nullable, .day⟩ := by rw [csvField]; rfl
  have rows : dates.length = table.length := by
    have lengths := congrArg List.length slots
    simpa [Arrow.DateStream.FromCsv.slots] using lengths
  exact ⟨table, checked, group, decoded, opened, read, agrees.1,
    agrees.2.1.trans (congrArg Date.FromIpc.leaf field), agrees.2.2.1,
    agrees.2.2.2.1.trans rows, days.trans slots⟩

end Silmaril.Proofs.Formats.Parquet.Date.FromCsv
