module

public import Silmaril.Formats.Parquet.ByteArrayFallback.File.Defs
import Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.File.Trace

/-! Exact footer order, one batch per complete group and original indexed errors. -/

public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.File

open Silmaril.Formats.Arrow Silmaril.Relational

variable {name : String} {checked : ByteArrayFallback.Checked name}
variable {limits : ByteArrayFallback.Limits} {input : Bytes}

/-- A batch preserves every opaque slot and the full group length. -/
theorem batch_slots (name : String) (slots : List (Option Bytes)) (field : Fin (schema name).width) :
    let batch := AlignedColumns.ofRows (Plain.ByteArray.File.rows name .optional slots)
    batch.rowCount = slots.length ∧ batch.values field = slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.File.batch_slots name slots field

/-- The event trace follows the original footer ordinals on one checked snapshot. -/
theorem readAll_order (opened : ByteArrayFallback.openFile limits input name = .ok checked) :
    let trace := Reader.denoteGroups (rowsAt checked limits) (List.range checked.snapshot.groupCount)
    readAll limits input name = .ok ⟨schema name, ⟨trace.1.map AlignedColumns.ofRows, trace.2⟩⟩ :=
  Proofs.Formats.Parquet.ByteArrayFallback.File.readAll_order opened

/-- Each successful indexed group becomes exactly one batch, including an empty group. -/
theorem readAll_success {groups : List (List (Option Bytes))}
    (opened : ByteArrayFallback.openFile limits input name = .ok checked)
    (decoded : List.Forall₂ (fun index slots => ByteArrayFallback.readGroup checked limits index = .ok slots)
      (List.range checked.snapshot.groupCount) groups) :
    readAll limits input name = .ok ⟨schema name,
      ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional), .eos⟩⟩ :=
  Proofs.Formats.Parquet.ByteArrayFallback.File.readAll_success opened decoded

/-- The first failed group retains its cause and all complete earlier batches. -/
theorem readAll_first_error {before after : List Nat} {index : Nat}
    {groups : List (List (Option Bytes))} {cause : ByteArrayFallback.Error}
    (opened : ByteArrayFallback.openFile limits input name = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i slots => ByteArrayFallback.readGroup checked limits i = .ok slots) before groups)
    (failed : ByteArrayFallback.readGroup checked limits index = .error cause) :
    readAll limits input name = .ok ⟨schema name,
      ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional),
        .readError (.readFailure cause)⟩⟩ :=
  Proofs.Formats.Parquet.ByteArrayFallback.File.readAll_first_error opened split earlier failed

/-- An open failure occurs before any group or schema is emitted. -/
theorem readAll_open_error {cause : Plain.ByteArray.File.Error}
    (failed : ByteArrayFallback.openFile limits input name = .error cause) :
    readAll limits input name = .error (.openFailure cause) := by
  rw [readAll, openSource, failed]
  rfl

end Silmaril.Formats.Parquet.ByteArrayFallback.File
