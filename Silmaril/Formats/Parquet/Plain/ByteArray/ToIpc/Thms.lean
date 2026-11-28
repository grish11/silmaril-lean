module

public import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Defs
import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Thms
import Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.ToIpc.Correctness

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc

open Silmaril.Relational
open Arrow.BinaryView
open Relational.BinaryObservation (observation observeIpc)

variable {parquet : File.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
variable {input : Bytes} {name : String} {layout : FlatColumn.Layout} {wire : KBytes}

/-- The conversion succeeds exactly when source exhaustion and native stream
emission both succeed. -/
theorem convert_ok_iff :
    convert parquet ipc view input name layout = .ok wire ↔
      ∃ source, readSource parquet input name layout = .ok source ∧
        StreamWriter.emit ipc view source.ipcField source.batches = .ok wire :=
  Proofs.Formats.Parquet.Plain.ByteArray.ToIpc.convert_ok_iff

/-- Successful native wire recovers the exact descriptor and every footer
group's ordered nullable octets, even for a group with zero rows. -/
theorem convert_readback (written : convert parquet ipc view input name layout = .ok wire) :
    ∃ (checked : File.Checked name layout) (groups : List (List (Option Bytes)))
      (batches : List (List (Option KBytes))),
      File.openFile parquet input name layout = .ok checked ∧
      (List.range checked.snapshot.groupCount).mapM (checked.readGroup parquet) = .ok groups ∧
      Stream.read ipc view wire = .ok ⟨⟨name, decide (layout = .optional), .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) =
        groups.map (List.map (Option.map Bytes.toList)) ∧
      batches.map List.length = groups.map List.length ∧ batches.length = checked.snapshot.groupCount ∧
      observeIpc ⟨name, decide (layout = .optional)⟩ ipc view wire =
        .ok (observation ⟨name, decide (layout = .optional)⟩ (groups.flatten.map (Option.map Bytes.toList))) :=
  Proofs.Formats.Parquet.Plain.ByteArray.ToIpc.convert_readback written

theorem convert_open_error {cause : File.Error}
    (failed : File.openFile parquet input name layout = .error cause) :
    convert parquet ipc view input name layout = .error (.source (.openError cause)) := by
  simp [convert, readSource_open_error failed, Except.mapError, Bind.bind, Except.bind]

/-- The indexed source error is returned before any wire can be published.
The underlying source trace still contains the complete preceding groups. -/
theorem convert_first_error {checked : File.Checked name layout} {before after : List Nat} {index : Nat}
    {groups : List (List (Option Bytes))} {cause : FlatColumn.Error File.PageError}
    (opened : File.openFile parquet input name layout = .ok checked)
    (indices : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.readGroup parquet) = .ok groups)
    (failed : checked.readGroup parquet index = .error cause) :
    convert parquet ipc view input name layout = .error (.source (.readError cause)) ∧
      File.readAll parquet input name layout = .ok
        ⟨File.schema name layout,
          ⟨groups.map (AlignedColumns.ofRows ∘ File.rows name layout), .readError (.column cause)⟩⟩ := by
  obtain ⟨error, trace⟩ := readSource_first_error opened indices earlier failed
  exact ⟨by simp [convert, error, Except.mapError, Bind.bind, Except.bind], trace⟩

/-- Writer errors occur after complete source preparation and keep their
original stage, index and cause. -/
theorem convert_writer_error {source : Source} {cause : StreamWriter.Error}
    (prepared : readSource parquet input name layout = .ok source)
    (failed : StreamWriter.emit ipc view source.ipcField source.batches = .error cause) :
    convert parquet ipc view input name layout = .error (.writer cause) := by
  simp [convert, prepared, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc
