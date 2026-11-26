module

public import Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet.Defs
import Silmaril.Proofs.Formats.Relational.NamedTable.MixedIpc.Interchange.Correctness

/-! Observation-preserving interchange between the selected mixed Parquet
profile and independently supplied mixed IPC streams. -/

public section

namespace Silmaril.Formats.Relational.NamedTable.MixedIpc.Interchange

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Relational
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet

/-- At the same exact descriptor, a table records just the ordered nullable pairs. -/
theorem table_eq_iff {left right : Prepared} (same : left.descriptor = right.descriptor) :
    left.table = right.table ↔ left.batches.flatten = right.batches.flatten :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.Interchange.table_eq_iff same

/-- Under each path’s admission limits, exact descriptor and a vacant name, the two imports
produce the same database exactly when the ordered pairs from the checked Parquet
groups match the IPC rows. Group and batch sizes may differ. -/
theorem imports_agree_iff {Name : Type*} [DecidableEq Name]
    (db : Database Name) (key : Name) (vacant : db key = none)
    {parquet : File.Limits} {intermediate direct : MixedIpc.Limits} {input : Bytes}
    {int32 byteArray : Field} {wire other : KBytes} {ipc : Prepared}
    (converted : ToIpc.convert parquet intermediate.mixed input int32 byteArray = .ok wire)
    (fits : wire.len ≤ intermediate.inputBytes)
    (read : MixedIpc.read direct other = .ok ipc)
    (same : ipc.descriptor = descriptor int32 byteArray) :
    (∃ next, importNamed db key parquet intermediate input int32 byteArray = .ok next ∧
      importIpc db key (descriptor int32 byteArray) direct other = .ok next) ↔
      ∃ (checked : File.Checked parquet int32 byteArray) (groups : List (List Row)),
        File.openFile parquet input int32 byteArray = .ok checked ∧
        (List.range checked.projection.snapshot.groupCount).mapM
          (checked.projection.readGroup parquet.group) = .ok groups ∧
        (groups.map groupPairs).flatten = ipc.batches.flatten :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.Interchange.imports_agree_iff db key vacant converted fits read same

end Silmaril.Formats.Relational.NamedTable.MixedIpc.Interchange
