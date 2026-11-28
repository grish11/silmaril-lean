module

public import Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet.Defs
import Silmaril.Proofs.Formats.Relational.NamedTable.MixedIpc.FromParquet.Correctness

public section

namespace Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup

variable {parquet : File.Limits} {ipc : MixedIpc.Limits} {input : Bytes}
variable {int32 byteArray : Field} {wire : KBytes}

/-- The same native limits and a sufficient IPC carrier cap admit the exact selected, grouped source observation. -/
theorem convert_observation
    (converted : ToIpc.convert parquet ipc.mixed input int32 byteArray = .ok wire)
    (bounded : wire.len ≤ ipc.inputBytes) :
    ∃ (checked : File.Checked parquet int32 byteArray) (groups : List (List Row)),
      File.openFile parquet input int32 byteArray = .ok checked ∧
      (List.range checked.projection.snapshot.groupCount).mapM
        (checked.projection.readGroup parquet.group) = .ok groups ∧
      MixedIpc.read ipc wire = .ok (observation int32 byteArray groups) :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.FromParquet.convert_observation converted bounded

/-- Success requires a vacant destination, successful conversion and the IPC carrier cap.
The only update stores the original selected rows in footer order with batch boundaries flattened. -/
theorem importNamed_ok_iff {Name : Type*} [DecidableEq Name] (db next : Database Name) (name : Name)
    (parquet : File.Limits) (ipc : MixedIpc.Limits) (input : Bytes) (int32 byteArray : Field) :
    importNamed db name parquet ipc input int32 byteArray = .ok next ↔
      db name = none ∧ ∃ (wire : KBytes) (checked : File.Checked parquet int32 byteArray)
        (groups : List (List Row)),
        ToIpc.convert parquet ipc.mixed input int32 byteArray = .ok wire ∧ wire.len ≤ ipc.inputBytes ∧
        File.openFile parquet input int32 byteArray = .ok checked ∧
        (List.range checked.projection.snapshot.groupCount).mapM
          (checked.projection.readGroup parquet.group) = .ok groups ∧
        let table := (observation int32 byteArray groups).table
        next = Function.update db name (some ⟨table.schema, table.rows⟩) :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.FromParquet.importNamed_ok_iff db next name parquet ipc input int32 byteArray

/-- Preserve the exact original source or writer failure before invoking insertion. -/
theorem importNamed_conversion_error {Name : Type*} [DecidableEq Name]
    (db : Database Name) (name : Name) {cause : ToIpc.Error}
    (failed : ToIpc.convert parquet ipc.mixed input int32 byteArray = .error cause) :
    importNamed db name parquet ipc input int32 byteArray = .error (.conversion cause) := by
  simp [importNamed, failed]

/-- After successful conversion, an IPC or destination failure returns its
original typed cause and no updated database. -/
theorem importNamed_ipc_error {Name : Type*} [DecidableEq Name]
    (db : Database Name) (name : Name) {cause : NamedTable.ImportError MixedIpc.Error}
    (converted : ToIpc.convert parquet ipc.mixed input int32 byteArray = .ok wire)
    (failed : importIpc db name (descriptor int32 byteArray) ipc wire = .error cause) :
    importNamed db name parquet ipc input int32 byteArray = .error (.ipcImport cause) := by
  simp [importNamed, converted, failed, Except.mapError]

end Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet
