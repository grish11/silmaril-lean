module

public import Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet.Defs
import Silmaril.Formats.Relational.NamedTable.MixedIpc.Thms
import Silmaril.Formats.Relational.NamedTable.MixedIpc.Export.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Thms

public section

namespace Silmaril.Proofs.Formats.Relational.NamedTable.MixedIpc.FromParquet

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Relational.NamedTable
open Silmaril.Formats.Relational.NamedTable.MixedIpc
open Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet

variable {parquet : File.Limits} {ipc : MixedIpc.Limits} {input : Bytes}
variable {int32 byteArray : Field} {wire : KBytes}

private theorem groupObservation_eq (int32 byteArray : Field) (rows : List Row) :
    ToIpc.groupObservation int32 byteArray rows =
      Export.observePairs (descriptor int32 byteArray) (groupPairs rows) := by
  simp [ToIpc.groupObservation, Export.observePairs, groupPairs, descriptor,
    Prepare.Schema.ofSelection, Descriptor.intField, Descriptor.viewField,
    List.map_map, Function.comp_def]

theorem convert_observation
    (converted : ToIpc.convert parquet ipc.mixed input int32 byteArray = .ok wire)
    (bounded : wire.len ≤ ipc.inputBytes) :
    ∃ (checked : File.Checked parquet int32 byteArray) (groups : List (List Row)),
      File.openFile parquet input int32 byteArray = .ok checked ∧
      (List.range checked.projection.snapshot.groupCount).mapM
        (checked.projection.readGroup parquet.group) = .ok groups ∧
      MixedIpc.read ipc wire = .ok (observation int32 byteArray groups) := by
  obtain ⟨checked, groups, decoded, opened, reads, parsed, fields, batches, _⟩ :=
    ToIpc.convert_readback converted
  refine ⟨checked, groups, opened, reads, Export.read_of_observed bounded parsed fields ?_⟩
  simp only [List.map_map]
  rw [batches]
  exact congrArg (fun f => groups.map f) (funext (groupObservation_eq int32 byteArray))

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
        next = Function.update db name (some ⟨table.schema, table.rows⟩) := by
  cases converted : ToIpc.convert parquet ipc.mixed input int32 byteArray with
  | error cause => simp [importNamed, converted]
  | ok wire =>
    have stages : importNamed db name parquet ipc input int32 byteArray = .ok next ↔
        importIpc db name (descriptor int32 byteArray) ipc wire = .ok next := by
      simp only [importNamed, converted]
      cases importIpc db name (descriptor int32 byteArray) ipc wire <;> simp [Except.mapError]
    rw [stages, importIpc_ok_iff]
    constructor
    · rintro ⟨vacant, prepared, read, _, update⟩
      have bounded := (read_exact read).1
      obtain ⟨checked, groups, opened, reads, observed⟩ := convert_observation converted bounded
      rw [observed] at read
      cases read
      exact ⟨vacant, wire, checked, groups, rfl, bounded, opened, reads, update⟩
    · rintro ⟨vacant, otherWire, checked, groups, equal, bounded, opened, reads, update⟩
      cases equal
      obtain ⟨actual, actualGroups, actualOpen, actualReads, observed⟩ :=
        convert_observation converted bounded
      rw [opened] at actualOpen
      cases actualOpen
      rw [reads] at actualReads
      cases actualReads
      exact ⟨vacant, observation int32 byteArray groups, observed, rfl, update⟩

end Silmaril.Proofs.Formats.Relational.NamedTable.MixedIpc.FromParquet
