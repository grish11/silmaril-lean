module

public import Silmaril.Formats.Parquet.Int96.File.Defs
import Silmaril.Proofs.Formats.Parquet.Int96.File.Read

public section

namespace Silmaril.Formats.Parquet.Int96.File

variable {name : String} {layout : FlatColumn.Layout} {interpretation : Policy}

/-- Opening retains the original checked bytes, selected binding, and limits. -/
theorem openFile_sound {limits : Limits} {source : Bytes} {checked : Checked name layout interpretation}
    (opened : openFile limits source name layout interpretation = .ok checked) :
    source.length ≤ limits.maxFileBytes ∧
      Snapshot.check (Failure := Unit) limits.snapshot source = .ok checked.snapshot ∧
      checked.snapshot.metadata.numRows.toNat ≤ limits.maxTotalRows ∧
      FlatColumn.bindColumn checked.snapshot ⟨name, .int96, layout⟩ = .ok checked.binding ∧
      checked.columnLimits = limits.column :=
  Proofs.Formats.Parquet.Int96.File.openFile_sound opened

/-- The indexed read forwards the physical reader result and nested error unchanged. -/
theorem readGroup_eq_readColumn (checked : Checked name layout interpretation) (index : Nat) :
    checked.readGroup index =
      FlatColumn.readColumn checked.binding checked.columnLimits plain
        (decodePage interpretation checked.columnLimits) index := rfl

/-- A read uses the original chunk and page bodies in order and keeps the
footer count. -/
theorem readGroup_wire {checked : Checked name layout interpretation} {index : Nat}
    {slots : Slots interpretation} (read : checked.readGroup index = .ok slots) :
    ∃ group, FlatColumn.ColumnWire checked.binding checked.columnLimits
      (decodePage interpretation checked.columnLimits) index group slots :=
  Proofs.Formats.Parquet.Int96.File.readGroup_wire read

/-- Completion covers every footer ordinal. An error retains exactly the
successful prefix and original cause. -/
theorem readAll_sound (checked : Checked name layout interpretation) :
    let indices := List.range checked.snapshot.groupCount
    let trace := checked.readAll
    match trace.failure with
    | none => indices.mapM checked.readGroup = .ok trace.groups
    | some cause =>
      ∃ before index after, indices = before ++ index :: after ∧
        before.mapM checked.readGroup = .ok trace.groups ∧ checked.readGroup index = .error cause :=
  Proofs.Formats.Parquet.Int96.File.readAll_sound checked

/-- Successful ordered reads publish every complete group. -/
theorem readAll_complete {checked : Checked name layout interpretation} {groups : List (Slots interpretation)}
    (decoded : (List.range checked.snapshot.groupCount).mapM checked.readGroup = .ok groups) :
    checked.readAll = ⟨groups, none⟩ :=
  Proofs.Formats.Parquet.Int96.File.readAll_complete decoded

/-- The failing group contributes no rows and the unchanged cause terminates
the trace. -/
theorem readAll_first_error {checked : Checked name layout interpretation}
    {before after : List Nat} {index : Nat} {groups : List (Slots interpretation)} {cause : ReadError}
    (split : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM checked.readGroup = .ok groups)
    (failed : checked.readGroup index = .error cause) :
    checked.readAll = ⟨groups, some cause⟩ :=
  Proofs.Formats.Parquet.Int96.File.readAll_first_error split earlier failed

end Silmaril.Formats.Parquet.Int96.File
