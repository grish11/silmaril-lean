module

public import Silmaril.Formats.Relational.NamedTable.MixedIpc.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Stream.Thms
import Silmaril.Proofs.Formats.Relational.NamedTable.MixedIpc.Correctness

@[expose] public section

namespace Silmaril.Formats.Relational.NamedTable.MixedIpc

open Silmaril.Formats
open Silmaril.Formats.Arrow
open Silmaril.Relational

/-- The descriptor retains the original ordered names, nullability and kinds. -/
theorem descriptor_exact {fields : List MixedFlat.Field} {descriptor : Descriptor}
    (found : Descriptor.ofFields fields = some descriptor) : fields = descriptor.fields :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.descriptor_exact found

/-- The relational schema retains the original order and both exact labels. -/
theorem Descriptor.schema_columns (descriptor : Descriptor) :
    List.ofFn descriptor.schema.kind =
      (if descriptor.viewFirst then [(descriptor.binary, .binaryView), (descriptor.integer, .int32)]
        else [(descriptor.integer, .int32), (descriptor.binary, .binaryView)]) :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.schema_columns descriptor

/-- The positional schema identifies the full accepted descriptor. -/
theorem Descriptor.schema_injective : Function.Injective Descriptor.schema :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.schema_injective

/-- A decoded batch retains its row count and both full nullable columns, paired by row index. -/
theorem batchPairs_exact {descriptor : Descriptor} {batch : MixedFlat.Stream.Batch} {pairs : List Pair}
    (found : batchPairs descriptor batch = some pairs) :
    pairs.length = batch.observed.rowCount ∧
      ∃ bytes : List (Option KBytes),
        pairs.map Prod.snd = bytes.map (Option.map KBytes.toList) ∧
        let integer := (descriptor.intField, MixedFlat.Column.primitive
          (pairs.map fun pair => pair.1.map Arrow.Value.int32))
        let binary := (descriptor.viewField, MixedFlat.Column.binaryView bytes)
        batch.observed.columns = if descriptor.viewFirst then [binary, integer] else [integer, binary] :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.batchPairs_exact found

/-- A prepared observation comes from exact native stream success and retains every batch. -/
theorem read_exact {limits : Limits} {input : KBytes} {prepared : Prepared}
    (read : MixedIpc.read limits input = .ok prepared) :
    input.len ≤ limits.inputBytes ∧
    ∃ source : MixedFlat.Stream.Observed, MixedFlat.Stream.read limits.mixed input = .ok source ∧
      source.fields = prepared.descriptor.fields ∧
      List.Forall₂ (fun batch pairs => batchPairs prepared.descriptor batch = some pairs)
        source.batches prepared.batches :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.read_exact read

/-- Success is exactly a vacant destination, a checked observation and exact ordered schema.
The returned database updates just the destination with the flattened rows. -/
theorem importIpc_ok_iff {Name : Type*} [DecidableEq Name]
    (db next : Database Name) (name : Name) (expected : Descriptor) (limits : Limits) (input : KBytes) :
    importIpc db name expected limits input = .ok next ↔
      db name = none ∧ ∃ prepared : Prepared, MixedIpc.read limits input = .ok prepared ∧
        prepared.descriptor = expected ∧
        next = Function.update db name (some ⟨prepared.table.schema, prepared.table.rows⟩) :=
  (Proofs.Formats.Relational.NamedTable.MixedIpc.importIpc_ok_iff db next name expected limits input).trans (by
    simp only [Prepared.table, Descriptor.schema_injective.eq_iff])

/-- Two exact reads with the same flattened table give the same insertion.
Batch boundaries remain available separately from the database. -/
theorem importIpc_eq_of_table {Name : Type*} [DecidableEq Name]
    (db : Database Name) (name : Name) (expected : Descriptor)
    {limits : Limits} {left right : KBytes} {a b : Prepared}
    (leftRead : read limits left = .ok a) (rightRead : read limits right = .ok b)
    (equal : a.table = b.table) :
    importIpc db name expected limits left = importIpc db name expected limits right :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.importIpc_eq_of_table db name expected leftRead rightRead equal

/-- Source rejection yields only its classified error at a vacant destination. -/
theorem importIpc_openFailure {Name : Type*} [DecidableEq Name]
    {db : Database Name} {name : Name} (vacant : db name = none) (expected : Descriptor)
    {limits : Limits} {input : KBytes} {cause : Error}
    (failed : MixedIpc.read limits input = .error cause) :
    importIpc db name expected limits input = .error (classify (.openError cause)) :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.importIpc_openFailure vacant expected failed

/-- A late read error preserves its original batch index and cause, with no database result. -/
theorem importIpc_readFailure {Name : Type*} [DecidableEq Name]
    {db : Database Name} {name : Name} (vacant : db name = none) (expected : Descriptor)
    {limits : Limits} {input : KBytes} (within : input.len ≤ limits.inputBytes)
    {index : Nat} {cause : MixedFlat.Stream.BatchError}
    (failed : MixedFlat.Stream.read limits.mixed input = .error (.batch index cause)) :
    importIpc db name expected limits input = .error (.readError (.reader (.batch index cause))) :=
  Proofs.Formats.Relational.NamedTable.MixedIpc.importIpc_readFailure vacant expected within failed

/-- Exact reader framing through EOS is available for each prepared observation. -/
theorem read_wire {limits : Limits} {input : KBytes} {prepared : Prepared}
    (ok : read limits input = .ok prepared) :
    input.wf = true ∧ ∃ start source,
      MixedFlat.Stream.readSchemaFrame limits.mixed.observation.ipc input =
        .ok (prepared.descriptor.fields, start) ∧
      MixedFlat.Stream.BatchesWire limits.mixed input prepared.descriptor.fields
        limits.mixed.observation.ipc.batches 0 start source ∧
      List.Forall₂ (fun batch rows => batchPairs prepared.descriptor batch = some rows)
        source prepared.batches := by
  obtain ⟨_, decoded, success, fields, batches⟩ := read_exact ok
  obtain ⟨wf, start, schema, wire⟩ := (MixedFlat.Stream.read_iff _ _ _).mp success
  exact ⟨wf, start, decoded.batches, fields ▸ schema, fields ▸ wire, batches⟩

end Silmaril.Formats.Relational.NamedTable.MixedIpc
