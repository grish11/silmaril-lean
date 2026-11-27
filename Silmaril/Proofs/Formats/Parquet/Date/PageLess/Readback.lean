module

public import Silmaril.Formats.Parquet.Date.PageLess.Defs
import all Silmaril.Formats.Parquet.Date.Defs
import Silmaril.Formats.Parquet.Date.Events.Thms
import Silmaril.Formats.Parquet.Date.Events.ToIpc.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.PageLess

open Silmaril.Formats Parquet Date.PageLess
open Silmaril.Relational

private theorem denote_exact (checked : Date.Checked) (limits : Date.Limits)
    (indices : List Nat) :
    (∃ groups, indices.mapM (readGroup checked limits) = .ok groups ∧
      Reader.denoteGroups (rowsAt checked limits) indices = (groups.map (Date.Events.rows checked), .eos)) ↔
      (Reader.denoteGroups (rowsAt checked limits) indices).2 = .eos := by
  constructor
  · rintro ⟨_, _, same⟩
    simp [same]
  · induction indices with
    | nil => exact fun _ => ⟨[], rfl, rfl⟩
    | cons index indices ih =>
      intro terminated
      cases first : readGroup checked limits index with
      | error cause =>
        simp [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError] at terminated
      | ok group =>
        have trailing : (Reader.denoteGroups (rowsAt checked limits) indices).2 = .eos := by
          simpa [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError] using terminated
        obtain ⟨groups, decoded, ordered⟩ := ih trailing
        refine ⟨group :: groups, ?_, ?_⟩
        · simp [List.mapM_cons, first, decoded, Bind.bind, Except.bind, Pure.pure, Except.pure]
        · simp [Reader.denoteGroups, rowsAt, first, ordered, Except.map, Except.mapError]

theorem open_exact {limits : Date.Limits} {input : Bytes} {checked : Date.Checked}
    (opened : Date.openCheckedPageLess limits input = .ok checked) :
    Snapshot.checkPageLessInt32 limits.snapshot input = .ok checked.snapshot ∧
      Date.bind limits.snapshot.footer checked.snapshot = .ok checked.binding := by
  cases admitted : Snapshot.checkPageLessInt32 limits.snapshot input with
  | error cause =>
    simp [Date.openCheckedPageLess, admitted, Except.mapError, Bind.bind, Except.bind] at opened
  | ok snapshot =>
    cases bound : Date.bind limits.snapshot.footer snapshot with
    | error cause =>
      simp [Date.openCheckedPageLess, admitted, bound, Except.mapError, Bind.bind, Except.bind] at opened
    | ok binding =>
      simp [Date.openCheckedPageLess, admitted, bound, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at opened
      subst checked
      exact ⟨rfl, bound⟩

theorem readAll_eof {limits : Date.Limits} {input : Bytes} {observed : Observed}
    (read : readAll limits input = .ok observed) (eof : observed.2.termination = .eos) :
    ∃ checked groups, Date.openCheckedPageLess limits input = .ok checked ∧
      (List.range checked.snapshot.groupCount).mapM (readGroup checked limits) = .ok groups ∧
      groups.length = checked.snapshot.metadata.rowGroups.length ∧
      observed = ⟨Date.Events.schema checked,
        ⟨groups.map (AlignedColumns.ofRows ∘ Date.Events.rows checked), .eos⟩⟩ := by
  cases opened : Date.openCheckedPageLess limits input with
  | error cause => simp [readAll, opened, Bind.bind, Except.bind] at read
  | ok checked =>
    have same : observed = ⟨Date.Events.schema checked, trace checked limits⟩ := by
      simpa [readAll, opened, Bind.bind, Except.bind, Pure.pure, Except.pure, eq_comm] using read
    subst observed
    obtain ⟨groups, decoded, ordered⟩ :=
      (denote_exact checked limits _).mpr eof
    have lengths := (List.mapM_eq_ok_iff_forall₂.mp decoded).length_eq
    have original := Snapshot.checkPageLessInt32_exact (open_exact opened).1
    refine ⟨checked, groups, rfl, decoded, ?_, ?_⟩
    · simpa [original.2.2.2.1] using lengths.symm
    · simp [trace, ordered, List.map_map]

theorem toIpc_readback {limits : Date.Limits} {output : Arrow.ObservationLimits}
    {input : Bytes} {wire : KBytes} (written : toIpc limits output input = .ok wire) :
    ∃ checked groups, Date.openCheckedPageLess limits input = .ok checked ∧
      (List.range checked.snapshot.groupCount).mapM (readGroup checked limits) = .ok groups ∧
      groups.length = checked.snapshot.metadata.rowGroups.length ∧
      Arrow.DateStream.read output.ipc wire = .ok (Arrow.DateStream.Writer.observation
        checked.binding.leaf.name (checked.binding.leaf.repetition == some .optional)
        (groups.map (·.date32Slots))) := by
  cases read : readAll limits input with
  | error cause => simp [toIpc, read, Except.mapError, Bind.bind, Except.bind] at written
  | ok observed =>
    have emitted : Date.Events.ToIpc.emit output (.ok observed) = .ok wire := by
      cases emitted : Date.Events.ToIpc.emit output (.ok observed) with
      | error cause => simp [toIpc, read, emitted, Except.mapError, Bind.bind, Except.bind] at written
      | ok value =>
        simpa [toIpc, read, emitted, Except.mapError, Bind.bind, Except.bind] using written
    obtain ⟨schema, trace, column, name, nullable, admitted, eof, _, descriptor, ipc⟩ :=
      Date.Events.ToIpc.emit_readback emitted
    cases Except.ok.inj admitted
    obtain ⟨checked, groups, opened, decoded, count, same⟩ := readAll_eof read eof
    cases same
    rw [Date.Events.schema_field] at descriptor
    simp only [Prod.mk.injEq, Date.Events.Kind.date32.injEq] at descriptor
    obtain ⟨rfl, rfl⟩ := descriptor
    exact ⟨checked, groups, opened, decoded, count, by
      simpa only [Date.Events.ToIpc.batchSlots, List.map_map, Function.comp_def, Date.Events.batch_slots]
        using ipc⟩

end Silmaril.Proofs.Formats.Parquet.Date.PageLess
