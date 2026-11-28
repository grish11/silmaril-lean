module

public import Silmaril.Formats.Parquet.Date.PageLess.Defs
import Silmaril.Proofs.Formats.Parquet.Date.PageLess.Readback

public section

namespace Silmaril.Formats.Parquet.Date.PageLess

open Silmaril.Relational

/-- The profile checks the original footer before the same raw DATE binding. -/
theorem open_exact {limits : Date.Limits} {input : Bytes} {checked : Date.Checked}
    (opened : Date.openCheckedPageLess limits input = .ok checked) :
    Snapshot.checkPageLessInt32 limits.snapshot input = .ok checked.snapshot ∧
      Date.bind limits.snapshot.footer checked.snapshot = .ok checked.binding :=
  Proofs.Formats.Parquet.Date.PageLess.open_exact opened

/-- A framed group uses the existing scanner on the original checked snapshot. -/
theorem readGroup_framed {checked : Date.Checked} {limits : Date.Limits} {index : Nat}
    {group : Footer.RowGroup} (found : checked.snapshot.groupAt index = some group)
    (hasPages : Footer.PageLessInt32.isPageLess group = false) :
    readGroup checked limits index = checked.readGroup limits index := by
  simp [readGroup, found, hasPages]

/-- The exact page-less convention yields an indexed empty vector, after
checking its bound path and the existing flat schema limits. -/
theorem readGroup_pageLess {checked : Date.Checked} {limits : Date.Limits} {index : Nat}
    {group : Footer.RowGroup} {fields : List FlatScan.Field}
    (found : checked.snapshot.groupAt index = some group)
    (noPages : Footer.PageLessInt32.isPageLess group = true)
    (column : Date.checkColumn checked.binding group = .ok ())
    (schema : FlatScan.flatSchema (ε := FlatScan.AdapterError) limits.scan checked.snapshot.metadata.schema = .ok fields) :
    readGroup checked limits index = .ok ⟨checked.binding, 0, ⟨#[], rfl⟩⟩ := by
  simp [readGroup, found, noPages, column, schema, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

/-- EOF preserves every original group, its footer order, and the DATE descriptor. -/
theorem readAll_eof {limits : Date.Limits} {input : Bytes} {observed : Observed}
    (read : readAll limits input = .ok observed) (eof : observed.2.termination = .eos) :
    ∃ checked groups, Date.openCheckedPageLess limits input = .ok checked ∧
      (List.range checked.snapshot.groupCount).mapM (readGroup checked limits) = .ok groups ∧
      groups.length = checked.snapshot.metadata.rowGroups.length ∧
      observed = ⟨Date.Events.schema checked,
        ⟨groups.map (AlignedColumns.ofRows ∘ Date.Events.rows checked), .eos⟩⟩ :=
  Proofs.Formats.Parquet.Date.PageLess.readAll_eof read eof

/-- A schema-only file emits no batch. -/
theorem readAll_noGroups {limits : Date.Limits} {input : Bytes} {checked : Date.Checked}
    (opened : Date.openCheckedPageLess limits input = .ok checked)
    (count : checked.snapshot.groupCount = 0) :
    readAll limits input = .ok ⟨Date.Events.schema checked, ⟨[], .eos⟩⟩ := by
  simp [readAll, opened, trace, count, Reader.denoteGroups, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

/-- An admitted explicit page-less group emits an explicit zero-row batch. -/
theorem readAll_oneEmpty {limits : Date.Limits} {input : Bytes} {checked : Date.Checked}
    (opened : Date.openCheckedPageLess limits input = .ok checked)
    (count : checked.snapshot.groupCount = 1)
    (decoded : readGroup checked limits 0 = .ok ⟨checked.binding, 0, ⟨#[], rfl⟩⟩) :
    readAll limits input = .ok ⟨Date.Events.schema checked, ⟨[AlignedColumns.ofRows []], .eos⟩⟩ := by
  simp [readAll, opened, trace, count, List.range_succ, Reader.denoteGroups, rowsAt, decoded,
    Except.map, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    Date.Events.rows, Date.RowGroup.date32Slots]

/-- Native IPC retains the bound field and one exact nullable batch per
original group. An empty inner list remains an explicit zero-row batch. -/
theorem toIpc_readback {limits : Date.Limits} {output : Arrow.ObservationLimits}
    {input : Bytes} {wire : KBytes} (written : toIpc limits output input = .ok wire) :
    ∃ checked groups, Date.openCheckedPageLess limits input = .ok checked ∧
      (List.range checked.snapshot.groupCount).mapM (readGroup checked limits) = .ok groups ∧
      groups.length = checked.snapshot.metadata.rowGroups.length ∧
      Arrow.DateStream.read output.ipc wire = .ok (Arrow.DateStream.Writer.observation
        checked.binding.leaf.name (checked.binding.leaf.repetition == some .optional)
        (groups.map (·.date32Slots))) :=
  Proofs.Formats.Parquet.Date.PageLess.toIpc_readback written

end Silmaril.Formats.Parquet.Date.PageLess
