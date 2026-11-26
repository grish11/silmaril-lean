module

public import Silmaril.Formats.Relational.NamedTable.MixedIpc.Export.Defs
import Silmaril.Proofs.Formats.Relational.NamedTable.MixedIpc.Export.Correctness

public section

namespace Silmaril.Formats.Relational.NamedTable.MixedIpc.Export

open Silmaril.Relational
open Silmaril.Formats.Arrow.MixedFlat

/-- Reading both typed positions and rebuilding a row preserves that row. -/
theorem row_rowPair (descriptor : Descriptor) (row : Scan.Row descriptor.schema Cell) :
    descriptor.row (rowPair descriptor row) = row :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.Export.row_rowPair descriptor row

/-- Successful preparation yields every stored row, split in order at exactly the requested sizes. -/
theorem prepare_exact {Name : Type*} {db : Database Name} {name : Name}
    {expected : Descriptor} {sizes : List Nat} {batches : List (List Pair)}
    (prepared : Export.prepare db name expected sizes = .ok batches) :
    ∃ rows : Scan.Table expected.schema Cell,
      Scan.observePacked db name = some ⟨expected.schema, rows⟩ ∧
      sizes.sum = rows.length ∧ batches = (sizes.splitLengths rows).map (List.map (rowPair expected)) :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.Export.prepare_exact prepared

/-- Success consists of exact table preparation, the raw octet and final carrier caps, and native writer success. -/
theorem emit_ok_iff {Name : Type*} (db : Database Name) (name : Name)
    (expected : Descriptor) (sizes : List Nat) (limits : MixedIpc.Limits) (wire : KBytes) :
    Export.emit db name expected sizes limits = .ok wire ↔
      ∃ batches, Export.prepare db name expected sizes = .ok batches ∧
        octetBytes batches ≤ limits.inputBytes ∧
        StreamWriter.emit limits.mixed (writerSchema expected) (batches.map writerBatch) = .ok wire ∧
        wire.len ≤ limits.inputBytes :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.Export.emit_ok_iff db name expected sizes limits wire

/-- The emitted bytes read through EOS at the original descriptor and requested batch sizes.
Flattening recovers the exact stored typed table. -/
theorem emit_readback {Name : Type*} {db : Database Name} {name : Name}
    {expected : Descriptor} {sizes : List Nat} {limits : MixedIpc.Limits} {wire : KBytes}
    (written : Export.emit db name expected sizes limits = .ok wire) :
    ∃ rows : Scan.Table expected.schema Cell, ∃ prepared : Prepared,
      Scan.observePacked db name = some ⟨expected.schema, rows⟩ ∧
      MixedIpc.read limits wire = .ok prepared ∧
      prepared.descriptor = expected ∧
      prepared.batches = (sizes.splitLengths rows).map (List.map (rowPair expected)) ∧
      prepared.batches.map List.length = sizes ∧
      prepared.table = ⟨expected.schema, rows⟩ :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.Export.emit_readback written

/-- With the same limits, importing at a vacant destination inserts exactly the original table. -/
theorem emit_import {Name Target : Type*} [DecidableEq Target]
    {db : Database Name} {name : Name} {expected : Descriptor} {sizes : List Nat}
    {limits : MixedIpc.Limits} {wire : KBytes} (written : Export.emit db name expected sizes limits = .ok wire)
    (dest : Database Target) (key : Target) (vacant : dest key = none) :
    ∃ rows : Scan.Table expected.schema Cell,
      Scan.observePacked db name = some ⟨expected.schema, rows⟩ ∧
      importIpc dest key expected limits wire =
        .ok (Function.update dest key (some ⟨expected.schema, rows⟩)) :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.Export.emit_import written dest key vacant

end Silmaril.Formats.Relational.NamedTable.MixedIpc.Export
