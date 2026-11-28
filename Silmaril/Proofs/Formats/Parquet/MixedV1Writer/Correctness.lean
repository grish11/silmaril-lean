module

public import Silmaril.Formats.Parquet.MixedV1Writer.Defs
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.MixedV1Writer

open Silmaril.Formats.Parquet Silmaril.Formats.Parquet.MixedV1Writer

theorem emit_checked {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    input.Valid limits ∧ output.Checked limits input ∧
    readback limits.readback input output = .ok input.rows := by
  by_cases valid : input.Valid limits
  · cases assembled : assemble limits input with
    | error cause => simp [emit, valid, assembled, Bind.bind, Except.bind] at written
    | ok candidate =>
      by_cases checked : candidate.Checked limits input
      · cases read : readback limits.readback input candidate with
        | error cause => simp [emit, valid, assembled, checked, read, Except.mapError, Bind.bind, Except.bind] at written
        | ok rows =>
          by_cases same : rows = input.rows
          · simp [emit, valid, assembled, checked, read, same, Except.mapError, Bind.bind, Except.bind,
              pure, Except.pure] at written
            subst output
            exact ⟨valid, checked, read.trans (congrArg Except.ok same)⟩
          · simp [emit, valid, assembled, checked, read, same, Except.mapError, Bind.bind, Except.bind, throw] at written
      · simp [emit, valid, assembled, checked, Bind.bind, Except.bind, throw] at written
  · simp [emit, valid] at written

theorem rows_exact {input : Input} {limits : Limits} (valid : input.Valid limits) :
    input.rows.length = input.rowCount ∧ input.rows.map Prod.fst = input.integers.slots ∧
      input.rows.map Prod.snd = input.octets.slots := by
  have left : input.integers.slots.length = input.rowCount := by
    unfold Input.rowCount
    cases input.integers <;> simp [PlainV1Writer.Input.slots, PlainV1Writer.Input.numValues]
  have right : input.octets.slots.length = input.octets.numValues := by
    cases input.octets <;> simp [PlainByteArrayV1Writer.Input.slots, PlainByteArrayV1Writer.Input.numValues]
  have aligned := left.trans (valid.2.2.2.1.trans right.symm)
  exact ⟨by simp [Input.rows, List.length_zip, aligned, right, ← valid.2.2.2.1],
    List.map_fst_zip (Nat.le_of_eq aligned), List.map_snd_zip (Nat.le_of_eq aligned.symm)⟩

theorem emit_wire {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    ∃ opened : Int32ByteArrayGroup.Checked input.intField input.byteField,
      Int32ByteArrayGroup.openFile limits.readback output.bytes input.intField input.byteField = .ok opened ∧
      Int32ByteArrayGroup.GroupWire opened limits.readback 0 input.rows := by
  have read := (emit_checked written).2.2
  unfold readback at read
  cases opened : Int32ByteArrayGroup.openFile limits.readback output.bytes input.intField input.byteField with
  | error cause => simp [opened, Except.bind] at read
  | ok checked =>
    simp [opened, Except.bind] at read
    exact ⟨checked, rfl, Int32ByteArrayGroup.readGroup_wire read⟩

end Silmaril.Proofs.Formats.Parquet.MixedV1Writer
