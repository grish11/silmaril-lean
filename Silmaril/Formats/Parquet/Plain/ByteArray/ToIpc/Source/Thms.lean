module

public import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Defs
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.ToIpc.Source

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc

open Silmaril.Relational
open Arrow.BinaryView
open Relational.BinaryObservation

/-- A prepared source contains exactly the selected descriptor and all
successful original group reads in footer order. -/
theorem readSource_ok_iff {limits : File.Limits} {input : Bytes} {name : String}
    {layout : FlatColumn.Layout} {source : Source} :
    readSource limits input name layout = .ok source ↔
      ∃ checked : File.Checked name layout, File.openFile limits input name layout = .ok checked ∧
        (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits) = .ok source.groups ∧
        source.field = ⟨name, decide (layout = .optional)⟩ :=
  Proofs.Formats.Parquet.Plain.ByteArray.ToIpc.readSource_ok_iff

/-- Successful preparation witnesses full exhaustion and exactly one
writer batch per checked footer group. -/
theorem readSource_eos {limits : File.Limits} {input : Bytes} {name : String}
    {layout : FlatColumn.Layout} {source : Source} (success : readSource limits input name layout = .ok source) :
    ∃ checked : File.Checked name layout, File.openFile limits input name layout = .ok checked ∧
      source.batches.length = checked.snapshot.groupCount ∧
      File.readAll limits input name layout = .ok
        ⟨File.schema name layout,
          ⟨source.groups.map (AlignedColumns.ofRows ∘ File.rows name layout), .eos⟩⟩ :=
  Proofs.Formats.Parquet.Plain.ByteArray.ToIpc.readSource_eos success

/-- The complete-source handoff returns the original open error. -/
theorem readSource_open_error {limits : File.Limits} {input : Bytes} {name : String}
    {layout : FlatColumn.Layout} {cause : File.Error}
    (failed : File.openFile limits input name layout = .error cause) :
    readSource limits input name layout = .error (.openError cause) := by
  simp [readSource, failed, Except.mapError, Bind.bind, Except.bind]

/-- A failed indexed read returns its original cause without a prepared source.
The abstract source trace still carries the preceding complete groups. -/
theorem readSource_first_error {limits : File.Limits} {input : Bytes} {name : String}
    {layout : FlatColumn.Layout} {checked : File.Checked name layout} {before after : List Nat} {index : Nat}
    {groups : List (List (Option Bytes))} {cause : FlatColumn.Error File.PageError}
    (opened : File.openFile limits input name layout = .ok checked)
    (indices : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.readGroup limits) = .ok groups)
    (failed : checked.readGroup limits index = .error cause) :
    readSource limits input name layout = .error (.readError cause) ∧
      File.readAll limits input name layout = .ok
        ⟨File.schema name layout,
          ⟨groups.map (AlignedColumns.ofRows ∘ File.rows name layout), .readError (.column cause)⟩⟩ :=
  Proofs.Formats.Parquet.Plain.ByteArray.ToIpc.readSource_first_error opened indices earlier failed

theorem packValue_wf (value : Bytes) : (packValue value).wf = true :=
  Arrow.Writer.emitWords_wf 1 _

theorem packValue_octets (value : Bytes) : (packValue value).toList = value.toList :=
  Proofs.Formats.Parquet.Plain.ByteArray.ToIpc.packValue_octets value

/-- Normalization preserves every nullable octet slot within its group. -/
theorem batches_octets (source : Source) :
    source.batches.map (List.map (Option.map KBytes.toList)) =
      source.groups.map (List.map (Option.map Bytes.toList)) :=
  Proofs.Formats.Parquet.Plain.ByteArray.ToIpc.batches_octets source

theorem batches_row_counts (source : Source) :
    source.batches.map List.length = source.groups.map List.length := by
  simp [Source.batches, List.map_map, Function.comp_def]

/-- Exact field and per-batch octet readback suffice for the existing
boundary-independent BinaryView observation. -/
theorem observeIpc_of_read (source : Source) {ipc : Arrow.Limits} {limits : Column.Limits}
    {wire : KBytes} {batches : List (List (Option KBytes))}
    (decoded : Stream.read ipc limits wire = .ok ⟨source.ipcField, batches⟩)
    (octets : batches.map (List.map (Option.map KBytes.toList)) =
      source.batches.map (List.map (Option.map KBytes.toList))) :
    observeIpc source.field ipc limits wire = .ok
      (observation source.field (source.groups.flatten.map (Option.map Bytes.toList))) :=
  Proofs.Formats.Parquet.Plain.ByteArray.ToIpc.observeIpc_of_read source decoded octets

end Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc
